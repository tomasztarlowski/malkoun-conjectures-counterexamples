"""Exact Malkoun G-amplitude & Conjecture D evaluator and adversarial scanner.

Reference: Joseph Malkoun, "Finite graphs and configurations of points",
arXiv:2508.13472v3 (Sept 7, 2026).
"""
from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
import itertools
import json
import math
from pathlib import Path
import time

import mpmath as mp
import networkx as nx
import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data"


def spinor_from_dir(v: np.ndarray) -> np.ndarray:
    """Return normalized +1-eigenvector of (v . sigma) in C^2 for unit vector v in R^3."""
    vx, vy, vz = float(v[0]), float(v[1]), float(v[2])
    if vz >= 0.0:
        u = 1.0 + vz
        denom = math.sqrt(2.0 * u)
        return np.array([u / denom, complex(vx, vy) / denom], dtype=np.complex128)
    u = 1.0 - vz
    denom = math.sqrt(2.0 * u)
    return np.array([complex(vx, -vy) / denom, u / denom], dtype=np.complex128)


def spinor_batch(dirs: np.ndarray) -> np.ndarray:
    """Vectorized +1-eigenvectors of (v . sigma) for an array of shape (..., 3) unit vectors."""
    vx = dirs[..., 0]
    vy = dirs[..., 1]
    vz = dirs[..., 2]
    out = np.empty(dirs.shape[:-1] + (2,), dtype=np.complex128)
    pos = vz >= 0.0
    if np.any(pos):
        u = 1.0 + vz[pos]
        denom = np.sqrt(2.0 * u)
        out[pos, 0] = u / denom
        out[pos, 1] = (vx[pos] + 1j * vy[pos]) / denom
    neg = ~pos
    if np.any(neg):
        u = 1.0 - vz[neg]
        denom = np.sqrt(2.0 * u)
        out[neg, 0] = (vx[neg] - 1j * vy[neg]) / denom
        out[neg, 1] = u / denom
    return out


def omega(phi1: np.ndarray, phi2: np.ndarray) -> complex:
    """Skew-symmetric bilinear form omega(phi1, phi2) = u1*v2 - u2*v1 on C^2."""
    return complex(phi1[0] * phi2[1] - phi1[1] * phi2[0])


@lru_cache(maxsize=16)
def _dicke_bitmask_table(deg: int) -> tuple[np.ndarray, np.ndarray]:
    """Return (hamming_weights, factorial_weights) for 2^deg multi-indices."""
    n_states = 1 << deg
    idx = np.arange(n_states, dtype=np.int64)
    hamming = np.zeros(n_states, dtype=np.int64)
    for b in range(deg):
        hamming += (idx >> b) & 1
    fact = np.array([math.factorial(k) for k in range(deg + 1)], dtype=np.float64)
    weights = fact[hamming] * fact[deg - hamming]
    return hamming, weights


def _symmetrized_vertex_tensor(psis: np.ndarray) -> np.ndarray:
    """Build sum_{pi in S_d} otimes_k psis[pi(k)] in O(d^2 + 2^d) without d! loop."""
    deg = psis.shape[0]
    if deg == 0:
        return np.array(1.0 + 0j, dtype=np.complex128)
    if deg == 1:
        return psis[0].copy()
    # Polynomial coefficients of prod_{r=0}^{d-1} (psis[r, 0] + t * psis[r, 1])
    poly = np.zeros(deg + 1, dtype=np.complex128)
    poly[0] = 1.0 + 0j
    for r in range(deg):
        a0, a1 = psis[r, 0], psis[r, 1]
        new_poly = np.zeros(deg + 1, dtype=np.complex128)
        new_poly[: r + 1] += poly[: r + 1] * a0
        new_poly[1 : r + 2] += poly[: r + 1] * a1
        poly = new_poly
    hamming, weights = _dicke_bitmask_table(deg)
    flat = weights * poly[hamming]
    return flat.reshape((2,) * deg)


def canonical_edges(edges: list[tuple[int, int]]) -> list[tuple[int, int]]:
    """Return deduplicated undirected edges sorted as (min(u,v), max(u,v))."""
    return sorted({(min(u, v), max(u, v)) for u, v in edges if u != v})


def g_amplitude_bruteforce(
    n_verts: int, edges: list[tuple[int, int]], points: np.ndarray
) -> complex:
    """Literal Eq. (13) evaluation by summing over P_G (for small-graph verification)."""
    edges_c = canonical_edges(edges)
    if not edges_c:
        return 1.0 + 0j

    pts = np.asarray(points, dtype=np.float64).reshape(n_verts, 3)
    # Build outgoing spinors per vertex
    out_edges: dict[int, list[int]] = {v: [] for v in range(n_verts)}
    spinors: dict[tuple[int, int], np.ndarray] = {}
    for u, w in edges_c:
        diff = pts[w] - pts[u]
        norm = float(np.linalg.norm(diff))
        if norm < 1e-15:
            raise ValueError(f"Degenerate edge ({u}, {w})")
        v_uw = diff / norm
        spinors[(u, w)] = spinor_from_dir(v_uw)
        spinors[(w, u)] = spinor_from_dir(-v_uw)
        out_edges[u].append(w)
        out_edges[w].append(u)

    denom = 1.0 + 0j
    for u, w in edges_c:
        denom *= omega(spinors[(u, w)], spinors[(w, u)])

    # P_G = prod_v Sym(N(v))
    vertex_lists = [v for v in range(n_verts) if out_edges[v]]
    per_vertex_perms = []
    for v in vertex_lists:
        nbrs = out_edges[v]
        per_vertex_perms.append([dict(zip(nbrs, perm)) for perm in itertools.permutations(nbrs)])

    total = 0.0 + 0j
    for choice in itertools.product(*per_vertex_perms):
        sigma_map = {v: mapping for v, mapping in zip(vertex_lists, choice)}
        prod_val = 1.0 + 0j
        for u, w in edges_c:
            w_mapped = sigma_map[u][w]
            u_mapped = sigma_map[w][u]
            prod_val *= omega(spinors[(u, w_mapped)], spinors[(w, u_mapped)])
        total += prod_val
    return total / denom


def _greedy_contract(tensors: list[tuple[list[int], np.ndarray]]) -> complex:
    """Contract closed tensor network of (edge_labels, array) greedily by min result rank."""
    active = list(tensors)
    while len(active) > 1:
        best_pair = None
        best_cost = None
        for i in range(len(active)):
            li = set(active[i][0])
            for j in range(i + 1, len(active)):
                lj = set(active[j][0])
                shared = li & lj
                if not shared:
                    continue
                result_rank = len(li ^ lj)
                max_operand = max(len(li), len(lj))
                cost = (result_rank, max_operand, len(li) + len(lj))
                if best_cost is None or cost < best_cost:
                    best_cost = cost
                    best_pair = (i, j)
        if best_pair is None:
            # Disconnected components: scalar multiply after contracting each component
            i, j = 0, 1
        else:
            i, j = best_pair
        labels_i, arr_i = active[i]
        labels_j, arr_j = active[j]
        shared_labels = [lbl for lbl in labels_i if lbl in labels_j]
        if shared_labels:
            axes_i = [labels_i.index(lbl) for lbl in shared_labels]
            axes_j = [labels_j.index(lbl) for lbl in shared_labels]
            arr_new = np.tensordot(arr_i, arr_j, axes=(axes_i, axes_j))
            labels_new = [lbl for lbl in labels_i if lbl not in shared_labels] + [
                lbl for lbl in labels_j if lbl not in shared_labels
            ]
        else:
            arr_new = np.multiply.outer(arr_i, arr_j)
            labels_new = labels_i + labels_j
        # Remove j then i (j > i)
        active.pop(j)
        active.pop(i)
        active.append((labels_new, arr_new))
    _, final_arr = active[0]
    return complex(np.asarray(final_arr).item())


def g_amplitude(n_verts: int, edges: list[tuple[int, int]], points: np.ndarray) -> complex:
    """Fast exact G-amplitude via closed symmetric Dicke tensor network contraction."""
    edges_c = canonical_edges(edges)
    if not edges_c:
        return 1.0 + 0j

    pts = np.asarray(points, dtype=np.float64).reshape(n_verts, 3)
    idx_u = np.array([e[0] for e in edges_c], dtype=np.int64)
    idx_v = np.array([e[1] for e in edges_c], dtype=np.int64)
    diffs = pts[idx_v] - pts[idx_u]
    norms = np.linalg.norm(diffs, axis=1)
    if np.any(norms < 1e-14):
        return complex(float("nan"), float("nan"))
    dirs = diffs / norms[:, None]

    psi_uv = spinor_batch(dirs)  # (m, 2)
    psi_vu = spinor_batch(-dirs)  # (m, 2)

    # omega(psi_uv, psi_vu) along each edge
    omegas = psi_uv[:, 0] * psi_vu[:, 1] - psi_uv[:, 1] * psi_vu[:, 0]
    denom = complex(np.prod(omegas))

    # Build vertex tensors. On source endpoint u of edge e=(u,w), apply skew matrix Omega
    # directly to that spinor BEFORE symmetrizing? Wait: check linearity!
    # Yes! Symmetrizing commutes with tensoring each leg by a linear map? NO!
    # Wait: the SAME spinors live at vertex u before sigma_u permutes them, and Omega is
    # applied to the FIXED slots (e_1, ..., e_d) AFTER symmetrization!
    # Wait: since Omega is the SAME 2x2 matrix on every outgoing edge slot of vertex u
    # (for u as source of edge e), Wait: vertex u might be source on some edges and target on
    # others! So Omega only acts on the legs where u is the source of Delta_Gamma.
    # Let's apply Omega on the source axis AFTER constructing T_u (via tensor slice swap)!
    vertex_legs: dict[int, list[tuple[int, bool]]] = {v: [] for v in range(n_verts)}
    for e_idx, (u, w) in enumerate(edges_c):
        vertex_legs[u].append((e_idx, True))
        vertex_legs[w].append((e_idx, False))

    omega_mat = np.array([[0.0, 1.0], [-1.0, 0.0]], dtype=np.complex128)
    tensors: list[tuple[list[int], np.ndarray]] = []
    for v in range(n_verts):
        legs = vertex_legs[v]
        if not legs:
            continue
        psis = np.stack(
            [psi_uv[e_idx] if is_src else psi_vu[e_idx] for e_idx, is_src in legs],
            axis=0,
        )
        t_v = _symmetrized_vertex_tensor(psis)
        for axis_k, (_, is_src) in enumerate(legs):
            if is_src:
                # Contract axis_k with Omega on its first index: sum_a T[..., a, ...] Omega[a, b]
                # Omega[0,1]=1, Omega[1,0]=-1 => new[..., 0] = -T[..., 1], new[..., 1] = T[..., 0]
                t_v = np.tensordot(t_v, omega_mat, axes=([axis_k], [0]))
                t_v = np.moveaxis(t_v, -1, axis_k)
        tensors.append(([e_idx for e_idx, _ in legs], t_v))

    num = _greedy_contract(tensors)
    return num / denom


def g_amplitude_mp(
    n_verts: int, edges: list[tuple[int, int]], points: list[list[float]], dps: int = 50
) -> mp.mpc:
    """High-precision arbitrary-dps verification for candidate counterexamples."""
    mp.mp.dps = dps
    edges_c = canonical_edges(edges)
    if not edges_c:
        return mp.mpc(1)

    pts = [[mp.mpf(c) for c in row] for row in points]
    spinors: dict[tuple[int, int], tuple[mp.mpc, mp.mpc]] = {}
    out_edges: dict[int, list[int]] = {v: [] for v in range(n_verts)}

    def _spinor_mp(vx: mp.mpf, vy: mp.mpf, vz: mp.mpf) -> tuple[mp.mpc, mp.mpc]:
        if vz >= 0:
            u = 1 + vz
            d = mp.sqrt(2 * u)
            return (mp.mpc(u) / d, mp.mpc(vx, vy) / d)
        u = 1 - vz
        d = mp.sqrt(2 * u)
        return (mp.mpc(vx, -vy) / d, mp.mpc(u) / d)

    def _omega_mp(a: tuple[mp.mpc, mp.mpc], b: tuple[mp.mpc, mp.mpc]) -> mp.mpc:
        return a[0] * b[1] - a[1] * b[0]

    for u, w in edges_c:
        dx = pts[w][0] - pts[u][0]
        dy = pts[w][1] - pts[u][1]
        dz = pts[w][2] - pts[u][2]
        nm = mp.sqrt(dx * dx + dy * dy + dz * dz)
        vx, vy, vz = dx / nm, dy / nm, dz / nm
        spinors[(u, w)] = _spinor_mp(vx, vy, vz)
        spinors[(w, u)] = _spinor_mp(-vx, -vy, -vz)
        out_edges[u].append(w)
        out_edges[w].append(u)

    denom = mp.mpc(1)
    for u, w in edges_c:
        denom *= _omega_mp(spinors[(u, w)], spinors[(w, u)])

    # Exact symmetric vertex tensors using mpmath
    vertex_legs: dict[int, list[tuple[int, bool]]] = {v: [] for v in range(n_verts)}
    for e_idx, (u, w) in enumerate(edges_c):
        vertex_legs[u].append((e_idx, True))
        vertex_legs[w].append((e_idx, False))

    # For small m or tree/bridge graphs we use exact Dicke tensor contraction in mpmath
    tensors: list[tuple[list[int], dict[tuple[int, ...], mp.mpc]]] = []
    for v in range(n_verts):
        legs = vertex_legs[v]
        if not legs:
            continue
        deg = len(legs)
        psis = [spinors[(v, edges_c[e_idx][1] if is_src else edges_c[e_idx][0])] for e_idx, is_src in legs]
        poly = [mp.mpc(0)] * (deg + 1)
        poly[0] = mp.mpc(1)
        for a0, a1 in psis:
            nxt = [mp.mpc(0)] * (deg + 1)
            for k in range(deg + 1):
                if poly[k] != 0:
                    nxt[k] += poly[k] * a0
                    if k + 1 <= deg:
                        nxt[k + 1] += poly[k] * a1
            poly = nxt
        tens: dict[tuple[int, ...], mp.mpc] = {}
        for bits in itertools.product((0, 1), repeat=deg):
            h = sum(bits)
            val = mp.factorial(h) * mp.factorial(deg - h) * poly[h]
            # Apply Omega on source legs: Omega[0,1]=1, Omega[1,0]=-1
            sign = 1
            out_bits = []
            for b, (_, is_src) in zip(bits, legs):
                if is_src:
                    if b == 1:
                        sign *= -1
                    out_bits.append(1 - b)
                else:
                    out_bits.append(b)
            tens[tuple(out_bits)] = val * sign
        tensors.append(([e_idx for e_idx, _ in legs], tens))

    # Contract greedily
    while len(tensors) > 1:
        best = None
        best_score = None
        for i in range(len(tensors)):
            si = set(tensors[i][0])
            for j in range(i + 1, len(tensors)):
                sj = set(tensors[j][0])
                if not (si & sj):
                    continue
                score = (len(si ^ sj), max(len(si), len(sj)))
                if best_score is None or score < best_score:
                    best_score = score
                    best = (i, j)
        i, j = best if best is not None else (0, 1)
        li, ti = tensors[i]
        lj, tj = tensors[j]
        shared = [x for x in li if x in lj]
        rem_i = [(k, x) for k, x in enumerate(li) if x not in shared]
        rem_j = [(k, x) for k, x in enumerate(lj) if x not in shared]
        pos_si = [li.index(x) for x in shared]
        pos_sj = [lj.index(x) for x in shared]
        new_labels = [x for _, x in rem_i] + [x for _, x in rem_j]
        # Group ti, tj by shared key
        grp_i: dict[tuple[int, ...], list[tuple[tuple[int, ...], mp.mpc]]] = {}
        for kbits, val in ti.items():
            skey = tuple(kbits[p] for p in pos_si)
            rkey = tuple(kbits[p] for p, _ in rem_i)
            grp_i.setdefault(skey, []).append((rkey, val))
        grp_j: dict[tuple[int, ...], list[tuple[tuple[int, ...], mp.mpc]]] = {}
        for kbits, val in tj.items():
            skey = tuple(kbits[p] for p in pos_sj)
            rkey = tuple(kbits[p] for p, _ in rem_j)
            grp_j.setdefault(skey, []).append((rkey, val))
        t_new: dict[tuple[int, ...], mp.mpc] = {}
        for skey, list_i in grp_i.items():
            list_j = grp_j.get(skey)
            if not list_j:
                continue
            for rki, vi in list_i:
                for rkj, vj in list_j:
                    nk = rki + rkj
                    t_new[nk] = t_new.get(nk, mp.mpc(0)) + vi * vj
        tensors.pop(j)
        tensors.pop(i)
        tensors.append((new_labels, t_new))

    return tensors[0][1][()] / denom


def _perm_small(mat: np.ndarray) -> complex:
    """Exact permanent of an n x n complex matrix (n <= 8)."""
    n = mat.shape[0]
    if n == 0:
        return 1.0 + 0j
    if n == 1:
        return complex(mat[0, 0])
    if n == 2:
        return complex(mat[0, 0] * mat[1, 1] + mat[0, 1] * mat[1, 0])
    if n == 3:
        return complex(
            mat[0, 0] * (mat[1, 1] * mat[2, 2] + mat[1, 2] * mat[2, 1])
            + mat[0, 1] * (mat[1, 0] * mat[2, 2] + mat[1, 2] * mat[2, 0])
            + mat[0, 2] * (mat[1, 0] * mat[2, 1] + mat[1, 1] * mat[2, 0])
        )
    # Ryser's formula
    total = 0.0 + 0j
    for mask in range(1, 1 << n):
        cols = [c for c in range(n) if (mask >> c) & 1]
        col_sums = mat[:, cols].sum(axis=1)
        prod_val = np.prod(col_sums)
        if (n - len(cols)) & 1:
            total -= prod_val
        else:
            total += prod_val
    return complex(total)


def partition_group_perms(blocks: list[list[int]], m: int) -> list[tuple[int, ...]]:
    """All permutations of [0..m-1] preserving each block in `blocks`."""
    block_perms = [list(itertools.permutations(b)) for b in blocks]
    result = []
    for combo in itertools.product(*block_perms):
        p = [0] * m
        for orig_b, perm_b in zip(blocks, combo):
            for idx_src, idx_dst in zip(orig_b, perm_b):
                p[idx_src] = idx_dst
        result.append(tuple(p))
    return result


def intersection_group_order(blocks1: list[list[int]], blocks2: list[list[int]]) -> int:
    """Compute |P_1 intersect P_2| = prod_{B, C} |B intersect C|!."""
    order = 1
    for b in blocks1:
        sb = set(b)
        for c in blocks2:
            k = len(sb & set(c))
            if k > 1:
                order *= math.factorial(k)
    return order


def conjecture_d_value(
    blocks1: list[list[int]],
    blocks2: list[list[int]],
    H: np.ndarray,
    perms1: list[tuple[int, ...]] | None = None,
) -> complex:
    """Compute f_{~1,~2}(H) using block permanent factorization over P_2."""
    m = H.shape[0]
    if perms1 is None:
        perms1 = partition_group_perms(blocks1, m)
    total = 0.0 + 0j
    for s1 in perms1:
        prod_val = 1.0 + 0j
        for c in blocks2:
            if len(c) == 1:
                idx = c[0]
                prod_val *= H[s1[idx], idx]
            else:
                rows = [s1[i] for i in c]
                sub = H[np.ix_(rows, c)]
                prod_val *= _perm_small(sub)
        total += prod_val
    return total


def tree_to_conjecture_d_setup(
    n_verts: int, edges: list[tuple[int, int]], points: np.ndarray
) -> tuple[list[list[int]], list[list[int]], np.ndarray]:
    """Build Theorem 4.1 (blocks1, blocks2, H) for a tree T and 3D configuration."""
    G = nx.Graph()
    G.add_nodes_from(range(n_verts))
    G.add_edges_from(edges)
    if not nx.is_tree(G):
        raise ValueError("Graph must be a tree")

    pts = np.asarray(points, dtype=np.float64).reshape(n_verts, 3)
    root = 0
    depths = nx.shortest_path_length(G, source=root)
    oriented_edges: list[tuple[int, int]] = []
    psis = []
    for u, w in nx.bfs_edges(G, source=root):
        # Parent is u, child is w, depth[w] = depth[u] + 1
        if depths[u] % 2 == 0:
            src, dst = u, w
        else:
            src, dst = w, u
        oriented_edges.append((src, dst))
        diff = pts[dst] - pts[src]
        v = diff / np.linalg.norm(diff)
        psis.append(spinor_from_dir(v))

    m = len(oriented_edges)
    by_src: dict[int, list[int]] = {}
    by_dst: dict[int, list[int]] = {}
    for idx, (src, dst) in enumerate(oriented_edges):
        by_src.setdefault(src, []).append(idx)
        by_dst.setdefault(dst, []).append(idx)

    blocks1 = list(by_src.values())
    blocks2 = list(by_dst.values())
    psi_mat = np.stack(psis, axis=0)  # (m, 2)
    # H_{ab} = <psi_a, psi_b> = conj(psi_a) . psi_b
    H = np.conj(psi_mat) @ psi_mat.T
    return blocks1, blocks2, H


def run_self_tests() -> dict:
    """Run all 6 mandatory mathematical invariant & benchmark self-tests."""
    rng = np.random.default_rng(20261120)
    results: dict[str, object] = {}

    # 1. Collinear K_n benchmarks: a_2=1, a_3=4, a_4=144
    for n, expected in [(2, 1.0), (3, 4.0), (4, 144.0)]:
        G = nx.complete_graph(n)
        pts = np.array([[0.0, 0.0, float(k)] for k in range(n)])
        val = g_amplitude(n, list(G.edges()), pts)
        bf = g_amplitude_bruteforce(n, list(G.edges()), pts)
        err = max(abs(val - expected), abs(bf - expected))
        assert err < 1e-10, f"Collinear K_{n} failed: got {val}, bf {bf}, expected {expected}"
        results[f"collinear_K{n}"] = {"val": val.real, "err": err}

    # 2 & 3. SO(3) invariance, translation invariance, reflection conjugation
    for name, G in [("K4", nx.complete_graph(4)), ("C4", nx.cycle_graph(4)), ("LG4", nx.path_graph(4))]:
        n = G.number_of_nodes()
        edges = list(G.edges())
        pts = rng.normal(size=(n, 3))
        val0 = g_amplitude(n, edges, pts)
        bf0 = g_amplitude_bruteforce(n, edges, pts)
        assert abs(val0 - bf0) < 1e-11, f"Tensor vs bruteforce mismatch on {name}: {val0} vs {bf0}"

        # Random SO(3) via QR
        A = rng.normal(size=(3, 3))
        Q, R = np.linalg.qr(A)
        Q = Q * np.sign(np.diag(R))
        if np.linalg.det(Q) < 0:
            Q[:, 0] *= -1.0
        shift = rng.normal(size=(1, 3)) * 5.0
        val_rot = g_amplitude(n, edges, pts @ Q.T + shift)
        assert abs(val_rot - val0) < 1e-10, f"SO(3)+trans failed on {name}"

        val_neg = g_amplitude(n, edges, -pts)
        assert abs(val_neg - np.conj(val0)) < 1e-10, f"Reflection conjugation failed on {name}"
        results[f"symmetries_{name}"] = {"abs_diff_bf": abs(val0 - bf0), "so3_err": abs(val_rot - val0)}

    # 4. Disjoint union multiplicativity
    G1 = nx.cycle_graph(3)
    G2 = nx.path_graph(3)
    G_disj = nx.disjoint_union(G1, G2)
    pts1 = rng.normal(size=(3, 3))
    pts2 = rng.normal(size=(3, 3))
    pts_all = np.vstack([pts1, pts2])
    a1 = g_amplitude(3, list(G1.edges()), pts1)
    a2 = g_amplitude(3, list(G2.edges()), pts2)
    a_disj = g_amplitude(6, list(G_disj.edges()), pts_all)
    err_disj = abs(a_disj - a1 * a2)
    assert err_disj < 1e-11, f"Disjoint union failed: {err_disj}"
    results["disjoint_union_err"] = err_disj

    # 5. Theorem 4.1 match on LG3, LG4, LG5, K_{1,3}
    for name, G in [
        ("LG3", nx.path_graph(3)),
        ("LG4", nx.path_graph(4)),
        ("LG5", nx.path_graph(5)),
        ("K1_3", nx.star_graph(3)),
    ]:
        n = G.number_of_nodes()
        edges = list(G.edges())
        pts = rng.normal(size=(n, 3))
        amp = g_amplitude(n, edges, pts)
        b1, b2, H = tree_to_conjecture_d_setup(n, edges, pts)
        f_val = conjecture_d_value(b1, b2, H)
        err_t41 = abs(amp - np.conj(f_val))
        assert err_t41 < 1e-11, f"Theorem 4.1 mismatch on {name}: {amp} vs conj({f_val})"
        results[f"theorem_4_1_{name}"] = err_t41

    # 6. Section 6 benchmark for K_{1,3}: collinear min=2, 3D |A| ~ 1.5054511, Re(A) ~ 1.5172676
    G_star = nx.star_graph(3)
    edges_star = list(G_star.edges())
    col_val = g_amplitude(4, edges_star, np.array([[0, 0, 0.0], [0, 0, 1.0], [0, 0, 2.0], [0, 0, -1.0]]))
    assert abs(col_val - 2.0) < 1e-12

    def _star_obj(x_flat: np.ndarray, mode: str) -> float:
        dirs = x_flat.reshape(3, 3)
        norms = np.linalg.norm(dirs, axis=1, keepdims=True)
        if np.any(norms < 1e-6):
            return 100.0
        pts = np.vstack([np.zeros((1, 3)), dirs / norms])
        val = g_amplitude(4, edges_star, pts)
        return abs(val) if mode == "abs" else val.real

    best_abs = 10.0
    best_real = 10.0
    for _ in range(16):
        x0 = rng.normal(size=9)
        r_abs = minimize(_star_obj, x0, args=("abs",), method="BFGS")
        best_abs = min(best_abs, float(r_abs.fun))
        r_re = minimize(_star_obj, x0, args=("real",), method="BFGS")
        best_real = min(best_real, float(r_re.fun))

    assert best_abs <= 1.5055, f"K_1,3 |A| opt failed: {best_abs}"
    assert best_real <= 1.5173, f"K_1,3 Re(A) opt failed: {best_real}"
    results["K1_3_benchmark"] = {
        "collinear": col_val.real,
        "min_abs": best_abs,
        "min_real": best_real,
        "paper_abs": 1.5054511,
        "paper_real": 1.5172676,
    }
    return results


def _all_partitions(seq: list[int]) -> list[list[list[int]]]:
    """Enumerate all set partitions of seq."""
    if len(seq) == 1:
        return [[seq]]
    first = seq[0]
    rest = _all_partitions(seq[1:])
    res = []
    for p in rest:
        res.append([[first]] + p)
        for i in range(len(p)):
            res.append(p[:i] + [[first] + p[i]] + p[i + 1 :])
    return res


def _refines(p1: list[list[int]], p2: list[list[int]]) -> bool:
    """True iff every block of p1 is contained in some block of p2."""
    sets2 = [set(b) for b in p2]
    for b in p1:
        sb = set(b)
        if not any(sb.issubset(c) for c in sets2):
            return False
    return True


def _canonical_partition_pair_key(b1: list[list[int]], b2: list[list[int]], m: int) -> tuple:
    """Approximate isomorphism invariant of (b1, b2) to prune symmetric duplicates."""
    deg1 = {x: len(blk) for blk in b1 for x in blk}
    deg2 = {x: len(blk) for blk in b2 for x in blk}
    inter = sorted(len(set(x) & set(y)) for x in b1 for y in b2 if set(x) & set(y))
    sig_b1 = tuple(sorted(tuple(sorted(deg2[x] for x in blk)) for blk in b1))
    sig_b2 = tuple(sorted(tuple(sorted(deg1[x] for x in blk)) for blk in b2))
    return (m, tuple(inter), sig_b1, sig_b2)


def _psd_from_params(theta: np.ndarray, m: int, rank: int) -> np.ndarray:
    """Build m x m unit-diagonal Hermitian PSD matrix H = L L* of given rank."""
    mat_raw = theta.reshape(m, rank, 2)
    L = mat_raw[:, :, 0] + 1j * mat_raw[:, :, 1]
    row_norms = np.linalg.norm(L, axis=1, keepdims=True)
    row_norms = np.maximum(row_norms, 1e-12)
    L = L / row_norms
    return L @ L.conj().T


def _optimize_conj_d_pair(task: tuple) -> dict:
    """Optimize Re(f(H))/|P1 cap P2| for a single partition pair (b1, b2)."""
    m, b1, b2, rank, n_starts, seed = task
    rng = np.random.default_rng(seed)
    perms1 = partition_group_perms(b1, m)
    denom = float(intersection_group_order(b1, b2))

    def obj(theta: np.ndarray) -> float:
        H = _psd_from_params(theta, m, rank)
        val = conjecture_d_value(b1, b2, H, perms1=perms1)
        return float(val.real / denom)

    best_ratio = float("inf")
    best_val = None
    best_theta = None

    for _ in range(n_starts):
        x0 = rng.normal(size=m * rank * 2)
        res = minimize(obj, x0, method="L-BFGS-B", options={"maxiter": 180, "ftol": 1e-12})
        if res.fun < best_ratio:
            best_ratio = float(res.fun)
            best_theta = res.x.copy()
            H = _psd_from_params(best_theta, m, rank)
            best_val = conjecture_d_value(b1, b2, H, perms1=perms1)

    return {
        "m": m,
        "rank": rank,
        "blocks1": b1,
        "blocks2": b2,
        "intersection_order": int(denom),
        "min_ratio_real": best_ratio,
        "min_complex_at_opt": [float(best_val.real), float(best_val.imag)] if best_val is not None else None,
        "best_H_real_diag_check": True,
        "best_theta": best_theta.tolist() if best_ratio < 0.999999 and best_theta is not None else None,
    }


def _optimize_graph(task: tuple) -> dict:
    """Optimize min Re(A_G(x)) and min |A_G(x)| for a connected graph G."""
    name, n_verts, edges, n_starts, seed = task
    rng = np.random.default_rng(seed)
    edges_c = canonical_edges(edges)

    def _unpack_pts(theta: np.ndarray) -> np.ndarray:
        # Fix x_0 = (0,0,0), x_1 on +z axis (only 1 param? no, allow full 3D for all except x_0=0)
        rest = theta.reshape(n_verts - 1, 3)
        return np.vstack([np.zeros((1, 3)), rest])

    def obj_real(theta: np.ndarray) -> float:
        pts = _unpack_pts(theta)
        # Keep edge lengths well-conditioned via mild scale barrier only if nearly colliding
        for u, w in edges_c:
            if np.linalg.norm(pts[w] - pts[u]) < 1e-6:
                return 1e6
        val = g_amplitude(n_verts, edges_c, pts)
        if math.isnan(val.real):
            return 1e6
        return float(val.real)

    def obj_abs(theta: np.ndarray) -> float:
        pts = _unpack_pts(theta)
        for u, w in edges_c:
            if np.linalg.norm(pts[w] - pts[u]) < 1e-6:
                return 1e6
        val = g_amplitude(n_verts, edges_c, pts)
        if math.isnan(val.real):
            return 1e6
        return float(abs(val))

    best_real = float("inf")
    best_real_pts = None
    best_abs = float("inf")
    best_abs_pts = None

    for k in range(n_starts):
        x0 = rng.normal(size=(n_verts - 1) * 3)
        # Mix normal 3D starts and perturbed nearly-collinear starts
        if k % 3 == 0:
            x0 = np.array([[0.05 * rng.normal(), 0.05 * rng.normal(), float(i + 1)] for i in range(n_verts - 1)]).ravel()
        r1 = minimize(obj_real, x0, method="BFGS", options={"maxiter": 160})
        if r1.fun < best_real:
            best_real = float(r1.fun)
            best_real_pts = _unpack_pts(r1.x).tolist()
        r2 = minimize(obj_abs, x0, method="BFGS", options={"maxiter": 160})
        if r2.fun < best_abs:
            best_abs = float(r2.fun)
            best_abs_pts = _unpack_pts(r2.x).tolist()

    return {
        "name": name,
        "n": n_verts,
        "m": len(edges_c),
        "edges": edges_c,
        "min_real": best_real,
        "min_abs": best_abs,
        "best_real_pts": best_real_pts if best_real < 1.005 else None,
        "best_abs_pts": best_abs_pts if best_abs < 1.005 else None,
    }


def _targeted_chiral_graphs() -> list[tuple[str, int, list[tuple[int, int]]]]:
    """Connected graphs on n=6..8 vertices designed to amplify chiral phase or path depth."""
    graphs: list[tuple[str, int, list[tuple[int, int]]]] = []
    # Path LG6 and LG7
    for n in (6, 7):
        g = nx.path_graph(n)
        graphs.append((f"LG{n}", n, list(g.edges())))
    # Cycles C5, C6, C7
    for n in (5, 6, 7):
        g = nx.cycle_graph(n)
        graphs.append((f"C{n}", n, list(g.edges())))
    # Double stars T_{2,2} (n=6), T_{3,3} (n=8), and spider graphs
    g_ds22 = nx.Graph([(0, 1), (0, 2), (0, 3), (3, 4), (3, 5)])
    graphs.append(("double_star_2_2", 6, list(g_ds22.edges())))
    g_ds33 = nx.Graph([(0, 1), (0, 2), (0, 3), (0, 4), (4, 5), (4, 6), (4, 7)])
    graphs.append(("double_star_3_3", 8, list(g_ds33.edges())))
    # 3-star chain of length 6 & 7
    g_comb6 = nx.Graph([(0, 1), (1, 2), (2, 3), (1, 4), (2, 5)])
    graphs.append(("caterpillar_6", 6, list(g_comb6.edges())))
    # Two K_{1,3} stars joined at leaf or bridge (n=7)
    g_two_stars = nx.Graph([(0, 1), (0, 2), (0, 3), (3, 4), (4, 5), (4, 6)])
    graphs.append(("bridged_stars_7", 7, list(g_two_stars.edges())))
    # Triangles / K4s joined by bridge or shared edge (chiral phase amplification!)
    g_bowtie5 = nx.Graph([(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)])
    graphs.append(("bowtie_5", 5, list(g_bowtie5.edges())))
    g_barbell_tri = nx.Graph([(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3)])
    graphs.append(("barbell_K3_6", 6, list(g_barbell_tri.edges())))
    g_barbell_k4 = nx.Graph(
        list(nx.complete_graph(4).edges())
        + [(3, 4)]
        + [(u + 4, v + 4) for u, v in nx.complete_graph(4).edges()]
    )
    graphs.append(("barbell_K4_8", 8, list(g_barbell_k4.edges())))
    # Complete K5 and K6 (Atiyah-Sutcliffe n=5, 6)
    graphs.append(("K5", 5, list(nx.complete_graph(5).edges())))
    # Wheel W6, Prism Y3, K_{3,3}, Petersen-subgraphs on n=6
    graphs.append(("W6", 6, list(nx.wheel_graph(6).edges())))
    graphs.append(("prism_6", 6, list(nx.circular_ladder_graph(3).edges())))
    graphs.append(("K3_3", 6, list(nx.complete_bipartite_graph(3, 3).edges())))
    # 2x3 grid and Octahedron
    graphs.append(("octahedron_6", 6, list(nx.octahedral_graph().edges())))
    return graphs


def run_sweeps(workers: int = 8) -> dict:
    """Execute Sweep A (Conjecture D) and Sweep B (Connected Graphs)."""
    t0 = time.monotonic()

    # Sweep A: incomparable non-trivial partition pairs on m=4,5
    conj_d_tasks = []
    seen_sigs = set()
    seed_counter = 100
    for m in (4, 5):
        parts = _all_partitions(list(range(m)))
        # Exclude trivial discrete (m blocks) and indiscrete (1 block)
        nontriv = [p for p in parts if 1 < len(p) < m]
        for b1 in nontriv:
            for b2 in nontriv:
                if _refines(b1, b2) or _refines(b2, b1):
                    continue
                sig = _canonical_partition_pair_key(b1, b2, m)
                if sig in seen_sigs:
                    continue
                seen_sigs.add(sig)
                # Test both rank-2 (spinor Gram) and full rank-m Hermitian PSD
                for rank in (2, m):
                    seed_counter += 1
                    conj_d_tasks.append((m, b1, b2, rank, 6, seed_counter))

    # Also explicitly add Theorem 4.1 setup for LG6 (m=5) and double_star_2_2 (m=5)
    for extra_name, G_extra in [("LG6_tree", nx.path_graph(6)), ("double_star_2_2_tree", nx.Graph([(0,1),(0,2),(0,3),(3,4),(3,5)]))]:
        b1, b2, _ = tree_to_conjecture_d_setup(G_extra.number_of_nodes(), list(G_extra.edges()), np.arange(G_extra.number_of_nodes() * 3, dtype=float).reshape(-1, 3) + 0.1)
        for rank in (2, 5):
            seed_counter += 1
            conj_d_tasks.append((5, b1, b2, rank, 12, seed_counter))

    # Sweep B: all connected n=4 (6), n=5 (21), plus targeted chiral n=6..8
    graph_tasks = []
    atlas = nx.graph_atlas_g()
    for G in atlas:
        n = G.number_of_nodes()
        if n in (4, 5) and nx.is_connected(G):
            seed_counter += 1
            graph_tasks.append((f"atlas_{G.name}_n{n}_m{G.number_of_edges()}", n, list(G.edges()), 10, seed_counter))

    seen_graph_names = {t[0] for t in graph_tasks}
    for gname, n, edges in _targeted_chiral_graphs():
        if gname in seen_graph_names:
            continue
        seed_counter += 1
        starts = 12 if n <= 6 else 8
        graph_tasks.append((gname, n, edges, starts, seed_counter))

    with ProcessPoolExecutor(max_workers=workers) as pool:
        conj_d_results = list(pool.map(_optimize_conj_d_pair, conj_d_tasks))
        graph_results = list(pool.map(_optimize_graph, graph_tasks))

    conj_d_sorted = sorted(conj_d_results, key=lambda r: r["min_ratio_real"])
    graph_sorted_real = sorted(graph_results, key=lambda r: r["min_real"])
    graph_sorted_abs = sorted(graph_results, key=lambda r: r["min_abs"])

    # High-precision check if any anomaly < 0.9999
    anomalies = []
    for r in graph_sorted_real[:5]:
        if r["min_real"] < 0.9999 and r["best_real_pts"] is not None:
            hp_val = g_amplitude_mp(r["n"], r["edges"], r["best_real_pts"], dps=50)
            anomalies.append({
                "kind": "graph_real",
                "name": r["name"],
                "float_val": r["min_real"],
                "mp50_real": str(mp.re(hp_val)),
                "mp50_imag": str(mp.im(hp_val)),
                "mp50_abs": str(abs(hp_val)),
            })
    for r in graph_sorted_abs[:5]:
        if r["min_abs"] < 0.9999 and r["best_abs_pts"] is not None:
            hp_val = g_amplitude_mp(r["n"], r["edges"], r["best_abs_pts"], dps=50)
            anomalies.append({
                "kind": "graph_abs",
                "name": r["name"],
                "float_val": r["min_abs"],
                "mp50_real": str(mp.re(hp_val)),
                "mp50_imag": str(mp.im(hp_val)),
                "mp50_abs": str(abs(hp_val)),
            })

    summary = {
        "duration_sec": round(time.monotonic() - t0, 2),
        "sweep_a_conj_d": {
            "total_pairs_tested": len(conj_d_results),
            "global_min_ratio_real": conj_d_sorted[0]["min_ratio_real"] if conj_d_sorted else None,
            "lowest_5": conj_d_sorted[:5],
            "violations_below_1": [r for r in conj_d_sorted if r["min_ratio_real"] < 0.9999],
        },
        "sweep_b_graphs": {
            "total_graphs_tested": len(graph_results),
            "global_min_real": graph_sorted_real[0]["min_real"] if graph_sorted_real else None,
            "global_min_abs": graph_sorted_abs[0]["min_abs"] if graph_sorted_abs else None,
            "lowest_8_by_real": [
                {k: v for k, v in r.items() if k not in ("best_real_pts", "best_abs_pts")}
                for r in graph_sorted_real[:8]
            ],
            "lowest_8_by_abs": [
                {k: v for k, v in r.items() if k not in ("best_real_pts", "best_abs_pts")}
                for r in graph_sorted_abs[:8]
            ],
            "violations_real_below_1": [r for r in graph_sorted_real if r["min_real"] < 0.9999],
            "violations_abs_below_1": [r for r in graph_sorted_abs if r["min_abs"] < 0.9999],
        },
        "mpmath_50dps_anomalies": anomalies,
    }
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description="Malkoun G-amplitude & Conjecture D scanner")
    parser.add_argument("--self-test", action="store_true", help="Run exact invariant checks")
    parser.add_argument("--sweep", action="store_true", help="Run Conjecture D and graph sweeps")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument(
        "--out",
        default=str(DATA_DIR / "malkoun_initial_scan.json"),
        help="Output JSON path for sweep results",
    )
    args = parser.parse_args()

    if args.self_test:
        res = run_self_tests()
        print(json.dumps({"self_test": "PASS", "details": res}, indent=2))
        if not args.sweep:
            return 0

    if args.sweep:
        summary = run_sweeps(workers=args.workers)
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
        print(json.dumps({
            "sweep": "DONE",
            "duration_sec": summary["duration_sec"],
            "conj_d_pairs": summary["sweep_a_conj_d"]["total_pairs_tested"],
            "conj_d_min_ratio": summary["sweep_a_conj_d"]["global_min_ratio_real"],
            "conj_d_violations": len(summary["sweep_a_conj_d"]["violations_below_1"]),
            "graphs_tested": summary["sweep_b_graphs"]["total_graphs_tested"],
            "graphs_min_real": summary["sweep_b_graphs"]["global_min_real"],
            "graphs_min_abs": summary["sweep_b_graphs"]["global_min_abs"],
            "graphs_violations_real": len(summary["sweep_b_graphs"]["violations_real_below_1"]),
            "graphs_violations_abs": len(summary["sweep_b_graphs"]["violations_abs_below_1"]),
            "out_file": str(out_path),
        }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
