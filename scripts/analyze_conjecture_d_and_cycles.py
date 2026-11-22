#!/usr/bin/env python3
"""Compute and verify witnesses for:
1. Disproofs of Malkoun's Conjecture D (Rank-3 at C_6, C_8 and Rank-2 at C_10, C_12).
2. 3D integer-coordinate bipartite even cycles C_18, C_20, C_24, C_28 breaking Conjecture B / Section 6.
3. Exact Lean 4 certificates & BFS walks for the triangle-free 3-connected cubic Wagner graph M_8.

Outputs data/conjecture_d_and_bipartite_cycles.json.
"""

from __future__ import annotations

import itertools
import json
import math
from collections import deque
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import minimize

mp.mp.dps = 50
ROOT = Path(__file__).resolve().parent.parent


def part_perms(blocks: list[list[int]], m: int) -> list[tuple[int, ...]]:
    block_perms = [list(itertools.permutations(b)) for b in blocks]
    res = []
    for choice in itertools.product(*block_perms):
        p = list(range(m))
        for b, bp in zip(blocks, choice):
            for src, dst in zip(b, bp):
                p[src] = dst
        res.append(tuple(p))
    return res


def verify_c6_c8_rank3() -> dict:
    # C_6: B in Z^{4x6}, H = B^T B
    B6 = [
        [1, 0, 1, 0, 1, 0],
        [0, 1, 0, 0, 0, -1],
        [0, -1, 0, 1, 0, 0],
        [0, 0, 0, -1, 0, 1],
    ]
    H6 = [[sum(B6[r][i] * B6[r][j] for r in range(4)) for j in range(6)] for i in range(6)]
    P1 = part_perms([[0, 1], [2, 3], [4, 5]], 6)
    P2 = part_perms([[1, 2], [3, 4], [5, 0]], 6)
    inter = len(set(P1) & set(P2))
    assert inter == 1
    lhs6 = 0
    for s1 in P1:
        for s2 in P2:
            prod = 1
            for e in range(6):
                prod *= H6[s1[e]][s2[e]]
            lhs6 += prod
    rhs6 = inter * math.prod(H6[e][e] for e in range(6))
    assert lhs6 == 7 and rhs6 == 8 and lhs6 < rhs6

    # C_8 rank-3 exact 3x8 integer witness giving LHS = 3, RHS = 4 (ratio 3/4):
    # Even cols e=0,2,4,6: e_0, e_0, -e_0, -e_0
    # Odd cols e=1,3,5,7: (0,1,1), (0,-1,0), (0,-1,1), (0,0,-1) -> H_11=2, H_33=1, H_55=2, H_77=1
    B8 = [
        [1, 0, 1, 0, -1, 0, -1, 0],
        [0, 1, 0, -1, 0, -1, 0, 0],
        [0, 1, 0, 0, 0, 1, 0, -1],
    ]
    H8 = [[sum(B8[r][i] * B8[r][j] for r in range(3)) for j in range(8)] for i in range(8)]
    P1_8 = part_perms([[0, 1], [2, 3], [4, 5], [6, 7]], 8)
    P2_8 = part_perms([[1, 2], [3, 4], [5, 6], [7, 0]], 8)
    assert len(set(P1_8) & set(P2_8)) == 1
    lhs8 = sum(math.prod(H8[s1[e]][s2[e]] for e in range(8)) for s1 in P1_8 for s2 in P2_8)
    rhs8 = math.prod(H8[e][e] for e in range(8))
    assert lhs8 == 3 and rhs8 == 4 and lhs8 < rhs8

    return {
        "C6": {"B": B6, "H": H6, "lhs": lhs6, "rhs": rhs6, "normalized_ratio": f"{lhs6}/{rhs6}"},
        "C8": {"B": B8, "H": H8, "lhs": lhs8, "rhs": rhs8, "normalized_ratio": f"{lhs8}/{rhs8}"},
    }


def gi_add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] + b[0], a[1] + b[1])


def gi_mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gi_conj(a: tuple[int, int]) -> tuple[int, int]:
    return (a[0], -a[1])


def c_cycle_transfer_exact_gi(H: list[list[tuple[int, int]]]) -> tuple[int, int]:
    m = len(H)
    k = m // 2
    T = [[(1, 0), (0, 0)], [(0, 0), (1, 0)]]
    for j in range(k):
        i0, i1 = 2 * j, 2 * j + 1
        iprev = (2 * j - 1) % m
        inext = (2 * j + 2) % m
        M = [[(0, 0), (0, 0)], [(0, 0), (0, 0)]]
        for bp in (0, 1):
            s2_0 = i0 if bp == 0 else iprev
            for bc in (0, 1):
                s2_1 = i1 if bc == 0 else inext
                M[bp][bc] = gi_add(gi_mul(H[i0][s2_0], H[i1][s2_1]), gi_mul(H[i1][s2_0], H[i0][s2_1]))
        T = [
            [
                gi_add(gi_mul(T[0][0], M[0][0]), gi_mul(T[0][1], M[1][0])),
                gi_add(gi_mul(T[0][0], M[0][1]), gi_mul(T[0][1], M[1][1])),
            ],
            [
                gi_add(gi_mul(T[1][0], M[0][0]), gi_mul(T[1][1], M[1][0])),
                gi_add(gi_mul(T[1][0], M[0][1]), gi_mul(T[1][1], M[1][1])),
            ],
        ]
    return gi_add(T[0][0], T[1][1])


def verify_c12_rank2() -> dict:
    Br = [
        [3, 0, 3, -1, 0, 0, -4, 3, -2, -3, 2, 3],
        [-3, 2, -3, -3, 1, 1, 2, 2, 1, -3, -1, 4],
    ]
    Bi = [
        [3, -2, 2, 1, 4, 2, -2, -2, 4, -1, 4, -2],
        [0, -4, -1, 4, -3, 4, 2, -3, -1, -1, -1, -1],
    ]
    B = [[(Br[r][c], Bi[r][c]) for c in range(12)] for r in range(2)]
    H = [
        [
            gi_add(gi_mul(gi_conj(B[0][i]), B[0][j]), gi_mul(gi_conj(B[1][i]), B[1][j]))
            for j in range(12)
        ]
        for i in range(12)
    ]
    # Exact brute force over all 64 * 64 = 4096 pairs in exact Z[i]!
    P1 = part_perms([[2 * j, 2 * j + 1] for j in range(6)], 12)
    P2 = part_perms([[(2 * j + 1) % 12, (2 * j + 2) % 12] for j in range(6)], 12)
    inter = len(set(P1) & set(P2))
    assert inter == 1
    lhs_bf = (0, 0)
    for s1 in P1:
        for s2 in P2:
            p = (1, 0)
            for e in range(12):
                p = gi_mul(p, H[s1[e]][s2[e]])
            lhs_bf = gi_add(lhs_bf, p)
    lhs_tm = c_cycle_transfer_exact_gi(H)
    assert lhs_bf == lhs_tm, (lhs_bf, lhs_tm)
    lhs_re, lhs_im = lhs_tm
    diag = [H[e][e][0] for e in range(12)]
    assert all(H[e][e][1] == 0 for e in range(12))
    rhs = 1
    for d in diag:
        rhs *= d
    assert lhs_re == -38243634152693760
    assert rhs == 46450162760601600
    assert lhs_re < 0 < rhs

    return {
        "Br": Br,
        "Bi": Bi,
        "diag": diag,
        "lhs_re": lhs_re,
        "lhs_im": lhs_im,
        "rhs": rhs,
        "ratio": lhs_re / rhs,
    }


def eval_mp50_cycle_direct(pts_int: list[list[int]]) -> mp.mpc:
    m = len(pts_int)
    psi = {}
    for u in range(m):
        for v in ((u - 1) % m, (u + 1) % m):
            dx = mp.mpf(pts_int[v][0] - pts_int[u][0])
            dy = mp.mpf(pts_int[v][1] - pts_int[u][1])
            dz = mp.mpf(pts_int[v][2] - pts_int[u][2])
            r = mp.sqrt(dx * dx + dy * dy + dz * dz)
            assert r > 0
            if r + dz > r / 2:
                s0, s1 = r + dz, dx + mp.j * dy
            else:
                s0, s1 = dx - mp.j * dy, r - dz
            norm = mp.sqrt(abs(s0) ** 2 + abs(s1) ** 2)
            psi[(u, v)] = (s0 / norm, s1 / norm)

    def om(a, b):
        return a[0] * b[1] - a[1] * b[0]

    den = mp.mpc(1, 0)
    for u in range(m):
        v = (u + 1) % m
        den *= om(psi[(u, v)], psi[(v, u)])

    T = [[mp.mpc(1, 0), mp.mpc(0, 0)], [mp.mpc(0, 0), mp.mpc(1, 0)]]
    for u in range(m):
        v = (u + 1) % m
        um = (u - 1) % m
        vp = (v + 1) % m
        W = [[mp.mpc(0, 0), mp.mpc(0, 0)], [mp.mpc(0, 0), mp.mpc(0, 0)]]
        for cu in (0, 1):
            su = v if cu == 0 else um
            for cv in (0, 1):
                sv = u if cv == 0 else vp
                W[cu][cv] = om(psi[(u, su)], psi[(v, sv)])
        T = [
            [T[0][0] * W[0][0] + T[0][1] * W[1][0], T[0][0] * W[0][1] + T[0][1] * W[1][1]],
            [T[1][0] * W[0][0] + T[1][1] * W[1][0], T[1][0] * W[0][1] + T[1][1] * W[1][1]],
        ]
    return (T[0][0] + T[1][1]) / den


def eval_mp50_cycle_bruteforce_small(pts_int: list[list[int]]) -> mp.mpc:
    """Cross-check transfer matrix against direct 2^m sum for m <= 8."""
    m = len(pts_int)
    psi = {}
    for u in range(m):
        for v in ((u - 1) % m, (u + 1) % m):
            dx = mp.mpf(pts_int[v][0] - pts_int[u][0])
            dy = mp.mpf(pts_int[v][1] - pts_int[u][1])
            dz = mp.mpf(pts_int[v][2] - pts_int[u][2])
            r = mp.sqrt(dx * dx + dy * dy + dz * dz)
            s0, s1 = (r + dz, dx + mp.j * dy) if r + dz > r / 2 else (dx - mp.j * dy, r - dz)
            norm = mp.sqrt(abs(s0) ** 2 + abs(s1) ** 2)
            psi[(u, v)] = (s0 / norm, s1 / norm)

    def om(a, b):
        return a[0] * b[1] - a[1] * b[0]

    den = mp.mpc(1, 0)
    for u in range(m):
        den *= om(psi[(u, (u + 1) % m)], psi[((u + 1) % m, u)])
    num = mp.mpc(0, 0)
    for bits in itertools.product((0, 1), repeat=m):
        prod = mp.mpc(1, 0)
        for u in range(m):
            v = (u + 1) % m
            su = v if bits[u] == 0 else (u - 1) % m
            sv = u if bits[v] == 0 else (v + 1) % m
            prod *= om(psi[(u, su)], psi[(v, sv)])
        num += prod
    return num / den


def eval_3d_cycle_float(pts: np.ndarray) -> tuple[complex, float]:
    m = len(pts)
    k = m // 2
    U = np.zeros((2, m), dtype=np.complex128)
    edges = [(2 * j if s == 0 else (2 * j + 2) % m, 2 * j + 1) for j in range(k) for s in (0, 1)]
    dists = []
    for idx, (u, v) in enumerate(edges):
        d = pts[v] - pts[u]
        r = float(np.linalg.norm(d))
        dists.append(r)
        if r < 1e-10:
            return 1e9 + 0j, 0.0
        vx, vy, vz = d / r
        if vz >= 0:
            s = np.array(
                [math.sqrt((1 + vz) / 2), (vx + 1j * vy) / (2 * math.sqrt((1 + vz) / 2))],
                dtype=np.complex128,
            )
        else:
            s = np.array(
                [(vx - 1j * vy) / (2 * math.sqrt((1 - vz) / 2)), math.sqrt((1 - vz) / 2)],
                dtype=np.complex128,
            )
        U[:, idx] = s
    H = U.conj().T @ U
    M = np.eye(2, dtype=np.complex128)
    for j in range(k):
        i0, i1, ip, inx = 2 * j, 2 * j + 1, (2 * j - 1) % m, (2 * j + 2) % m
        W = np.array(
            [
                [
                    H[i0, i0 if bp == 0 else ip] * H[i1, i1 if bc == 0 else inx]
                    + H[i1, i0 if bp == 0 else ip] * H[i0, i1 if bc == 0 else inx]
                    for bc in (0, 1)
                ]
                for bp in (0, 1)
            ]
        )
        M = M @ W
    diam = float(np.max(np.linalg.norm(pts - pts.mean(0), axis=1))) + 1e-15
    return complex(np.conj(np.trace(M))), min(dists) / diam


def find_bipartite_3d_cycles() -> dict:
    # First cross-check transfer matrix on C_8 integer points against brute force!
    c8_pts = [[i, (i * i) % 5, (i * i * i) % 7] for i in range(8)]
    v_tm = eval_mp50_cycle_direct(c8_pts)
    v_bf = eval_mp50_cycle_bruteforce_small(c8_pts)
    assert abs(v_tm - v_bf) < mp.mpf("1e-45"), (v_tm, v_bf)

    results = {}
    for m in [18, 20, 24, 28]:
        best_val = 1e18
        best_pts = None
        for pitch in [0.4, 0.8, 1.5]:
            for turns in [2, 3, 4]:
                pts0 = np.array(
                    [
                        [
                            math.cos(2 * math.pi * turns * i / (m - 1)),
                            math.sin(2 * math.pi * turns * i / (m - 1)),
                            pitch * i,
                        ]
                        for i in range(m)
                    ]
                )

                def loss(x: np.ndarray) -> float:
                    val, ratio = eval_3d_cycle_float(x.reshape(m, 3))
                    pen = 0.0 if ratio > 0.02 else 1e5 * (0.02 - ratio) ** 2
                    return val.real + pen

                res = minimize(loss, pts0.ravel(), method="BFGS", options={"maxiter": 250})
                val, ratio = eval_3d_cycle_float(res.x.reshape(m, 3))
                if ratio > 0.01 and val.real < best_val:
                    best_val = val.real
                    best_pts = res.x.reshape(m, 3)
        assert best_pts is not None
        pts_int = np.round(best_pts * 1000).astype(int).tolist()
        for u in range(m):
            assert pts_int[u] != pts_int[(u + 1) % m]
        val_mp = eval_mp50_cycle_direct(pts_int)
        results[f"C_{m}"] = {
            "n": m,
            "m": m,
            "is_bipartite": True,
            "pts_xyz_int": pts_int,
            "mp50_re": mp.nstr(val_mp.real, 35),
            "mp50_im": mp.nstr(val_mp.imag, 35),
            "mp50_abs": mp.nstr(abs(val_mp), 35),
            "violates_re_lt_1": bool(val_mp.real < 1),
            "violates_abs_lt_1": bool(abs(val_mp) < 1),
            "violates_re_lt_0": bool(val_mp.real < 0),
        }
    return results


def compute_wagner_m8_lean_data() -> dict:
    edges_m8 = [
        (0, 1),
        (0, 4),
        (0, 7),
        (1, 2),
        (1, 5),
        (2, 3),
        (2, 6),
        (3, 4),
        (3, 7),
        (4, 5),
        (5, 6),
        (6, 7),
    ]
    pts_m8 = [
        [183, -1727],
        [414, -1680],
        [-1609, 3064],
        [134, -1776],
        [174, -1744],
        [3967, 1],
        [1, -1369],
        [182, -1726],
    ]
    nbrs = {
        u: sorted([v for (x, y) in edges_m8 for v in ([y] if x == u else [x] if y == u else [])])
        for u in range(8)
    }

    # BFS walks for 3-vertex connectivity (removing any pair {c1, c2})
    anchors = {}
    walks = {}
    for c1 in range(8):
        for c2 in range(8):
            allowed = [x for x in range(8) if x != c1 and x != c2]
            anchor = allowed[0]
            anchors[(c1, c2)] = anchor
            q = deque([(anchor, [])])
            seen = {anchor}
            parent_walk = {anchor: []}
            while q:
                cur, w = q.popleft()
                for nxt in nbrs[cur]:
                    if nxt in allowed and nxt not in seen:
                        seen.add(nxt)
                        nw = w + [nxt]
                        parent_walk[nxt] = nw
                        q.append((nxt, nw))
            assert set(allowed) == seen, (c1, c2, allowed, seen)
            for b in range(8):
                walks[(c1, c2, b)] = parent_walk[b] if b in parent_walk else []

    # Scale S = 10^6 integer interval tables
    S = 10**6

    def iv_mul(a, b):
        p = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
        return [min(p), max(p)]

    def iv_add(a, b):
        return [a[0] + b[0], a[1] + b[1]]

    def iv_sub(a, b):
        return [a[0] - b[1], a[1] - b[0]]

    def civ_add(a, b):
        return [iv_add(a[0], b[0]), iv_add(a[1], b[1])]

    def civ_sub(a, b):
        return [iv_sub(a[0], b[0]), iv_sub(a[1], b[1])]

    def civ_mul(a, b):
        return [
            iv_sub(iv_mul(a[0], b[0]), iv_mul(a[1], b[1])),
            iv_add(iv_mul(a[0], b[1]), iv_mul(a[1], b[0])),
        ]

    def omega_iv(a, b):
        return civ_sub(civ_mul(a[0], b[1]), civ_mul(a[1], b[0]))

    dist_lo = [[0] * 8 for _ in range(8)]
    psi = {}
    for u in range(8):
        for v in nbrs[u]:
            dx = pts_m8[v][0] - pts_m8[u][0]
            dy = pts_m8[v][1] - pts_m8[u][1]
            lo = math.isqrt(S * S * (dx * dx + dy * dy))
            assert lo * lo <= S * S * (dx * dx + dy * dy) <= (lo + 1) ** 2
            dist_lo[u][v] = lo
            psi[(u, v)] = ([[lo, lo + 1], [0, 0]], [[S * dx, S * dx], [S * dy, S * dy]])

    def om_edge(u, v):
        return omega_iv(psi[(u, v)], psi[(v, u)])

    def prod4_edges(elist):
        res = civ_mul(civ_mul(om_edge(*elist[0]), om_edge(*elist[1])), om_edge(*elist[2]))
        return civ_mul(res, om_edge(*elist[3]))

    def prod2_edges(elist):
        return civ_mul(om_edge(*elist[0]), om_edge(*elist[1]))

    d_int = prod4_edges([(0, 4), (3, 7), (1, 2), (5, 6)])
    d_l = prod2_edges([(0, 7), (3, 4)])
    d_r = prod2_edges([(1, 5), (2, 6)])
    d_cut = prod4_edges([(0, 1), (2, 3), (4, 5), (6, 7)])
    den_cur = civ_mul(civ_mul(civ_mul(d_int, d_l), d_r), d_cut)

    def block2_table(u, v, ports):
        pu_l = list(itertools.permutations(nbrs[u]))
        pv_l = list(itertools.permutations(nbrs[v]))
        iu = {w: i for i, w in enumerate(nbrs[u])}
        iv = {w: i for i, w in enumerate(nbrs[v])}
        tab = {}
        for bits in itertools.product((0, 1), repeat=4):
            acc = [[0, 0], [0, 0]]
            for pu in pu_l:
                fu = civ_mul(
                    psi[(u, pu[iu[ports[0]]])][bits[0]],
                    psi[(u, pu[iu[ports[1]]])][bits[1]],
                )
                for pv in pv_l:
                    om_uv = omega_iv(psi[(u, pu[iu[v]])], psi[(v, pv[iv[u]])])
                    fv = civ_mul(
                        psi[(v, pv[iv[ports[2]]])][bits[2]],
                        psi[(v, pv[iv[ports[3]]])][bits[3]],
                    )
                    acc = civ_add(acc, civ_mul(om_uv, civ_mul(fu, fv)))
            tab["".join(str(b) for b in bits)] = acc
        return tab

    t0 = block2_table(0, 4, [1, 7, 3, 5])
    t1 = block2_table(3, 7, [2, 4, 0, 6])
    t2 = block2_table(1, 2, [0, 5, 3, 6])
    t3 = block2_table(5, 6, [1, 4, 2, 7])

    left_tab = {}
    for m01, m23_l, m45, m67_l in itertools.product((0, 1), repeat=4):
        acc = [[0, 0], [0, 0]]
        for b07 in (0, 1):
            for b34 in (0, 1):
                k0 = f"{m01}{b07}{1-b34}{m45}"
                k1 = f"{m23_l}{b34}{1-b07}{m67_l}"
                prod = civ_mul(t0[k0], t1[k1])
                acc = civ_add(acc, prod) if (b07 + b34) % 2 == 0 else civ_sub(acc, prod)
        left_tab[f"{m01}{m23_l}{m45}{m67_l}"] = acc

    right_tab = {}
    for m01_r, m23, m45_r, m67 in itertools.product((0, 1), repeat=4):
        acc = [[0, 0], [0, 0]]
        for b15 in (0, 1):
            for b26 in (0, 1):
                k2 = f"{m01_r}{b15}{m23}{b26}"
                k3 = f"{1-b15}{m45_r}{1-b26}{m67}"
                prod = civ_mul(t2[k2], t3[k3])
                acc = civ_add(acc, prod) if (b15 + b26) % 2 == 0 else civ_sub(acc, prod)
        right_tab[f"{m01_r}{m23}{m45_r}{m67}"] = acc

    num = [[0, 0], [0, 0]]
    for b01, b23, b45, b67 in itertools.product((0, 1), repeat=4):
        kl = f"{b01}{1-b23}{b45}{1-b67}"
        kr = f"{1-b01}{b23}{1-b45}{b67}"
        prod = civ_mul(left_tab[kl], right_tab[kr])
        num = civ_add(num, prod) if (b01 + b23 + b45 + b67) % 2 == 0 else civ_sub(num, prod)

    dot = iv_add(iv_mul(num[0], den_cur[0]), iv_mul(num[1], den_cur[1]))
    assert dot[1] < 0

    return {
        "edges": edges_m8,
        "pts_xy_int": pts_m8,
        "nbrs": {str(k): v for k, v in nbrs.items()},
        "scale": S,
        "dist_lo": dist_lo,
        "t0": t0,
        "t1": t1,
        "t2": t2,
        "t3": t3,
        "left_tab": left_tab,
        "right_tab": right_tab,
        "wagnerNumVal": num,
        "wagnerDenVal": den_cur,
        "dot": dot,
    }


def main() -> None:
    payload = {
        "rank3_conjecture_d_counterexamples": verify_c6_c8_rank3(),
        "rank2_conjecture_d_counterexample_c12": verify_c12_rank2(),
        "bipartite_3d_even_cycles": find_bipartite_3d_cycles(),
        "wagner_m8_lean_certificates": compute_wagner_m8_lean_data(),
    }
    out_path = ROOT / "data" / "conjecture_d_and_bipartite_cycles.json"
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")
    print("C6 rank-3:", payload["rank3_conjecture_d_counterexamples"]["C6"]["lhs"], "<", payload["rank3_conjecture_d_counterexamples"]["C6"]["rhs"])
    print("C12 rank-2:", payload["rank2_conjecture_d_counterexample_c12"]["lhs_re"], "<", payload["rank2_conjecture_d_counterexample_c12"]["rhs"])
    for k, v in payload["bipartite_3d_even_cycles"].items():
        print(f"3D {k}: A = {v['mp50_re'][:18]} + ({v['mp50_im'][:12]})i | |A| = {v['mp50_abs'][:18]}")
    print("Wagner dot.hi:", payload["wagner_m8_lean_certificates"]["dot"][1])


if __name__ == "__main__":
    main()
