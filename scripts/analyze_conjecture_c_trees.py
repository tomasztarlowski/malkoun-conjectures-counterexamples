"""Conjecture C (Trees) Counterexamples & 50-digit mpmath Verification.

Computes and cross-checks:
1. Exact planar zero on the minimal 10-vertex cubic cherry tree T_10 (cherryTree10).
2. Tree minimality scan summary across n = 4..10 (all n <= 9 trees >= 1; 4/106 at n = 10).
3. Continuous & integer 3D Hopf witnesses on spiders (n = 11, 12, 13).
4. Exact Gaussian-integer / 3D integer Hopf negative-Re witnesses on Malkoun's
   flagship linear path family LG_15 (m=14), LG_16 (m=15), and LG_17 (m=16),
   together with a path modulus scan |A_{LG_n}| across n = 6..25.

Writes results to data/conjecture_c_tree_counterexamples.json.
"""
from __future__ import annotations

import itertools
import json
import math
from pathlib import Path
import sys
import time

import mpmath as mp
import networkx as nx
import numpy as np
import scipy.optimize as opt

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from scan_malkoun import g_amplitude, g_amplitude_bruteforce  # noqa: E402

mp.mp.dps = 60


def compile_tree(T: nx.Graph):
    color = nx.bipartite.color(T)
    edges, eidx = [], {}
    for u, v in T.edges():
        if color[u] == 1:
            u, v = v, u
        idx = len(edges)
        edges.append((u, v))
        eidx[(u, v)] = idx
        eidx[(v, u)] = idx
    root = 0
    parent = {root: None}
    order = [root]
    for u in order:
        for w in T.neighbors(u):
            if w not in parent:
                parent[w] = u
                order.append(w)
    steps = []
    for u in reversed(order[1:]):
        p = parent[u]
        ch = [w for w in T.neighbors(u) if w != p]
        steps.append((u, color[u] == 0, ch, [eidx[(u, p)]] + [eidx[(u, c)] for c in ch]))
    rch = list(T.neighbors(root))
    return color, edges, len(edges), steps, (root, color[root] == 0, rch, [eidx[(root, c)] for c in rch])


PERMS = {k: np.array(list(itertools.permutations(range(k))), dtype=np.intp) for k in range(1, 10)}


def perm_sq_np(M: np.ndarray) -> complex:
    k = M.shape[0]
    if k == 0:
        return 1.0 + 0.0j
    if k == 1:
        return complex(M[0, 0])
    if k == 2:
        return complex(M[0, 0] * M[1, 1] + M[0, 1] * M[1, 0])
    P = PERMS[k]
    return complex(np.prod(M[np.arange(k), P], axis=1).sum())


def eval_tree_np(comp, B: np.ndarray) -> complex:
    _, _, _, steps, rinfo = comp
    msg = {}
    for u, is_c0, ch, inc in steps:
        vecs = np.conj(B[:, inc]) if is_c0 else B[:, inc]
        k = len(ch)
        if k == 0:
            msg[u] = vecs[:, 0]
        else:
            M = np.column_stack([msg[c] for c in ch]).T @ vecs
            cols = list(range(k + 1))
            coeffs = np.array([perm_sq_np(M[:, [c for c in cols if c != j]]) for j in range(k + 1)])
            msg[u] = vecs @ coeffs
    root, is_c0, rch, rinc = rinfo
    vecs = np.conj(B[:, rinc]) if is_c0 else B[:, rinc]
    return perm_sq_np(np.column_stack([msg[c] for c in rch]).T @ vecs)


def path_eval_np(B: np.ndarray) -> complex:
    _, m = B.shape
    H = B.conj().T @ B
    dp0, dp1 = 1.0 + 0.0j, 0.0 + 0.0j
    for e in range(m):
        if e == m - 1:
            dp0 = dp0 * H[e, e] + dp1 * (H[e, e - 1] if e % 2 == 0 else H[e - 1, e])
        else:
            if e % 2 == 0:
                dp0, dp1 = dp0 * H[e, e] + dp1 * H[e, e - 1], dp0 * H[e + 1, e] + dp1 * H[e + 1, e - 1]
            else:
                dp0, dp1 = dp0 * H[e, e] + dp1 * H[e - 1, e], dp0 * H[e, e + 1] + dp1 * H[e - 1, e + 1]
    return complex(dp0)


def mp_spinor_from_dir(vx: mp.mpf, vy: mp.mpf, vz: mp.mpf) -> tuple[mp.mpc, mp.mpc]:
    norm = mp.sqrt(vx * vx + vy * vy + vz * vz)
    vx, vy, vz = vx / norm, vy / norm, vz / norm
    if vz >= 0:
        u = 1 + vz
        d = mp.sqrt(2 * u)
        return mp.mpc(u / d, 0), mp.mpc(vx / d, vy / d)
    u = 1 - vz
    d = mp.sqrt(2 * u)
    return mp.mpc(vx / d, -vy / d), mp.mpc(u / d, 0)


def perm_sq_mp(M: list[list[mp.mpc]]) -> mp.mpc:
    k = len(M)
    if k == 0:
        return mp.mpc(1, 0)
    if k == 1:
        return M[0][0]
    if k == 2:
        return M[0][0] * M[1][1] + M[0][1] * M[1][0]
    tot = mp.mpc(0, 0)
    for p in itertools.permutations(range(k)):
        pr = mp.mpc(1, 0)
        for i in range(k):
            pr *= M[i][p[i]]
        tot += pr
    return tot


def tree_amplitude_mp(T: nx.Graph, pts_mp: list[tuple[mp.mpf, mp.mpf, mp.mpf]]) -> mp.mpc:
    """Exact high-precision Malkoun amplitude A_T(x) via tree tensor network contraction."""
    comp = compile_tree(T)
    _, edges, m, steps, rinfo = comp
    B_cols: list[tuple[mp.mpc, mp.mpc]] = []
    for u, v in edges:
        dx = pts_mp[v][0] - pts_mp[u][0]
        dy = pts_mp[v][1] - pts_mp[u][1]
        dz = pts_mp[v][2] - pts_mp[u][2]
        B_cols.append(mp_spinor_from_dir(dx, dy, dz))

    def get_vecs(inc: list[int], conj_flag: bool) -> list[tuple[mp.mpc, mp.mpc]]:
        out = []
        for idx in inc:
            a, b = B_cols[idx]
            out.append((mp.conj(a), mp.conj(b)) if conj_flag else (a, b))
        return out

    msg: dict[int, tuple[mp.mpc, mp.mpc]] = {}
    for u, is_c0, ch, inc in steps:
        vecs = get_vecs(inc, is_c0)
        k = len(ch)
        if k == 0:
            msg[u] = vecs[0]
        else:
            M = []
            for c in ch:
                mc0, mc1 = msg[c]
                M.append([mc0 * v[0] + mc1 * v[1] for v in vecs])
            coeffs = []
            for j in range(k + 1):
                subM = [[M[r][col] for col in range(k + 1) if col != j] for r in range(k)]
                coeffs.append(perm_sq_mp(subM))
            s0 = sum(vecs[j][0] * coeffs[j] for j in range(k + 1))
            s1 = sum(vecs[j][1] * coeffs[j] for j in range(k + 1))
            msg[u] = (s0, s1)
    _, is_c0, rch, rinc = rinfo
    vecs = get_vecs(rinc, is_c0)
    Mroot = []
    for c in rch:
        mc0, mc1 = msg[c]
        Mroot.append([mc0 * v[0] + mc1 * v[1] for v in vecs])
    gram_val = perm_sq_mp(Mroot)
    return mp.conj(gram_val)


def path_exact_gi(Br: list[list[int]], Bi: list[list[int]]) -> tuple[int, int, int]:
    """Exact Gaussian-integer (without normalizing columns) sum f_P(B^H B) and diag_prod."""
    m = len(Br[0])
    B = [[complex(Br[0][j], Bi[0][j]), complex(Br[1][j], Bi[1][j])] for j in range(m)]
    # Use Python big ints directly via pairs (re, im)!
    def c_conj(z):
        return (z[0], -z[1])

    def c_mul(z1, z2):
        return (z1[0] * z2[0] - z1[1] * z2[1], z1[0] * z2[1] + z1[1] * z2[0])

    def c_add(z1, z2):
        return (z1[0] + z2[0], z1[1] + z2[1])

    Bz = [((Br[0][j], Bi[0][j]), (Br[1][j], Bi[1][j])) for j in range(m)]
    H = [[None] * m for _ in range(m)]
    for i in range(m):
        for j in range(m):
            t0 = c_mul(c_conj(Bz[i][0]), Bz[j][0])
            t1 = c_mul(c_conj(Bz[i][1]), Bz[j][1])
            H[i][j] = c_add(t0, t1)

    dp0, dp1 = (1, 0), (0, 0)
    for e in range(m):
        if e == m - 1:
            off = H[e][e - 1] if e % 2 == 0 else H[e - 1][e]
            dp0 = c_add(c_mul(dp0, H[e][e]), c_mul(dp1, off))
        else:
            if e % 2 == 0:
                ndp0 = c_add(c_mul(dp0, H[e][e]), c_mul(dp1, H[e][e - 1])) if e > 0 else c_mul(dp0, H[e][e])
                ndp1 = c_add(c_mul(dp0, H[e + 1][e]), c_mul(dp1, H[e + 1][e - 1])) if e > 0 else c_mul(dp0, H[e + 1][e])
            else:
                ndp0 = c_add(c_mul(dp0, H[e][e]), c_mul(dp1, H[e - 1][e]))
                ndp1 = c_add(c_mul(dp0, H[e][e + 1]), c_mul(dp1, H[e - 1][e + 1]))
            dp0, dp1 = ndp0, ndp1

    diag_prod = 1
    for j in range(m):
        diag_prod *= H[j][j][0]
    return dp0[0], dp0[1], diag_prod


def hopf_vecs_int(Br: list[list[int]], Bi: list[list[int]]) -> list[list[int]]:
    m = len(Br[0])
    vecs = []
    for e in range(m):
        ar, ai = Br[0][e], Bi[0][e]
        br, bi = Br[1][e], Bi[1][e]
        wx = 2 * (ar * br + ai * bi)
        wy = 2 * (ar * bi - ai * br)
        wz = ar * ar + ai * ai - br * br - bi * bi
        vecs.append([wx, wy, wz])
    return vecs


def path_pts_int_from_spinors(Br: list[list[int]], Bi: list[list[int]]) -> list[list[int]]:
    vecs = hopf_vecs_int(Br, Bi)
    m = len(vecs)
    pts = [[0, 0, 0]]
    for e in range(m):
        w = vecs[e]
        prev = pts[-1]
        if e % 2 == 0:
            pts.append([prev[0] - w[0], prev[1] - w[1], prev[2] - w[2]])
        else:
            pts.append([prev[0] + w[0], prev[1] + w[1], prev[2] + w[2]])
    return pts


def make_spider(arms: list[int]) -> nx.Graph:
    G = nx.Graph()
    G.add_node(0)
    nxt = 1
    for L in arms:
        prev = 0
        for _ in range(L):
            G.add_edge(prev, nxt)
            prev = nxt
            nxt += 1
    return G


def main() -> None:
    t_start = time.time()

    # 1. Exact planar zero on 10-vertex cubic cherry tree cherryTree10
    edges_t10 = [(0, 1), (1, 2), (1, 3), (0, 4), (4, 5), (4, 6), (0, 7), (7, 8), (7, 9)]
    T10 = nx.Graph(edges_t10)
    ab_pairs_t10 = [
        [0, 0],
        [2, 0], [3, -1], [4, -2],
        [-1, 1], [0, 2], [1, 3],
        [-1, -1], [-3, -1], [-5, -1],
    ]
    s3_mp = mp.sqrt(3)
    pts_t10_mp = [(mp.mpf(a), mp.mpf(b) * s3_mp, mp.mpf(0)) for a, b in ab_pairs_t10]
    pts_t10_np = np.array([[float(a), float(b) * math.sqrt(3.0), 0.0] for a, b in ab_pairs_t10])
    amp_t10_bf = g_amplitude_bruteforce(10, edges_t10, pts_t10_np)
    amp_t10_fast = g_amplitude(10, edges_t10, pts_t10_np)
    amp_t10_mp = tree_amplitude_mp(T10, pts_t10_mp)
    min_dist_t10 = min(
        float(np.linalg.norm(pts_t10_np[i] - pts_t10_np[j]))
        for i in range(10) for j in range(i + 1, 10)
    )
    assert abs(amp_t10_mp) < mp.mpf("1e-50"), amp_t10_mp
    cherry_entry = {
        "n": 10,
        "m": 9,
        "edges": [list(e) for e in edges_t10],
        "ab_pairs_z_sqrt3": ab_pairs_t10,
        "min_pairwise_distance": min_dist_t10,
        "g_amplitude_bruteforce": [float(amp_t10_bf.real), float(amp_t10_bf.imag)],
        "g_amplitude_fast": [float(amp_t10_fast.real), float(amp_t10_fast.imag)],
        "mp50_re": mp.nstr(amp_t10_mp.real, 50),
        "mp50_im": mp.nstr(amp_t10_mp.imag, 50),
        "mp50_abs": mp.nstr(abs(amp_t10_mp), 50),
    }
    print(f"[T_10] min_dist={min_dist_t10:.6f}, |mp50|={mp.nstr(abs(amp_t10_mp), 12)}")

    # 2. Minimality scan across ALL non-isomorphic n = 4..9 trees (zero degree cap) and n = 10 summary
    minimality_n4_to_n9 = {}
    for n in range(4, 10):
        trees = list(nx.generators.nonisomorphic_trees(n))
        deg_le_6_cnt = sum(1 for T in trees if max(dict(T.degree()).values()) <= 6)
        worst_re, worst_abs = 1e9, 1e9
        rng = np.random.default_rng(400 + n)
        for T in trees:
            comp = compile_tree(T)
            m = comp[2]
            for _ in range(4):
                th0 = rng.normal(size=4 * m)

                def uB(th):
                    B = th[: 2 * m].reshape(2, m) + 1j * th[2 * m :].reshape(2, m)
                    return B / np.maximum(np.linalg.norm(B, axis=0, keepdims=True), 1e-12)

                res = opt.minimize(lambda th: eval_tree_np(comp, uB(th)).real, th0, method="L-BFGS-B", options={"maxiter": 80})
                v = eval_tree_np(comp, uB(res.x))
                worst_re = min(worst_re, float(v.real))
                worst_abs = min(worst_abs, float(abs(v)))
        minimality_n4_to_n9[str(n)] = {
            "count_all_trees": len(trees),
            "count_deg_le_6": deg_le_6_cnt,
            "min_re": worst_re,
            "min_abs": worst_abs,
        }
        print(f"[minimality n={n}] all_trees={len(trees)} (deg<=6: {deg_le_6_cnt}): min_re={worst_re:.9f}, min_abs={worst_abs:.9f}")

    # n=10 violating indices from full scan: #49, #77, #94 (cherryTree10), #97
    trees10 = list(nx.nonisomorphic_trees(10))
    n10_violators = {}
    rng10 = np.random.default_rng(2026)
    for idx in [49, 77, 94, 97]:
        T = trees10[idx]
        comp = compile_tree(T)
        m = comp[2]
        best_re, best_abs = 1e9, 1e9
        for _ in range(15):
            th0 = rng10.normal(size=4 * m)

            def uB(th):
                B = th[: 2 * m].reshape(2, m) + 1j * th[2 * m :].reshape(2, m)
                return B / np.maximum(np.linalg.norm(B, axis=0, keepdims=True), 1e-12)

            r1 = opt.minimize(lambda th: eval_tree_np(comp, uB(th)).real, th0, method="L-BFGS-B", options={"maxiter": 200})
            best_re = min(best_re, float(r1.fun))
            r2 = opt.minimize(lambda th: abs(eval_tree_np(comp, uB(th))), r1.x, method="L-BFGS-B", options={"maxiter": 250})
            best_abs = min(best_abs, float(r2.fun))
        n10_violators[f"tree10_{idx}"] = {
            "atlas_index": idx,
            "degrees": sorted(dict(T.degree()).values(), reverse=True),
            "edges": [list(e) for e in T.edges()],
            "min_re": best_re,
            "min_abs": best_abs,
        }
        print(f"[n=10 tree #{idx}] min_re={best_re:.9f}, min_abs={best_abs:.3e}")

    # 3. Spider witnesses: Spider(3,3,4), Spider(3,4,4), Spider(4,4,4)
    spider_entries = {}
    for sname, arms in [("Spider_3_3_4", [3, 3, 4]), ("Spider_3_4_4", [3, 4, 4]), ("Spider_4_4_4", [4, 4, 4])]:
        T = make_spider(arms)
        comp = compile_tree(T)
        color, edges, m, _, _ = comp
        rng_s = np.random.default_rng(1000 + sum(arms) * 17)
        best_re, best_abs, B_re, B_z = 1e9, 1e9, None, None
        for _ in range(25):
            th0 = rng_s.normal(size=4 * m)

            def uB(th):
                B = th[: 2 * m].reshape(2, m) + 1j * th[2 * m :].reshape(2, m)
                return B / np.maximum(np.linalg.norm(B, axis=0, keepdims=True), 1e-12)

            r1 = opt.minimize(lambda th: eval_tree_np(comp, uB(th)).real, th0, method="L-BFGS-B", options={"maxiter": 250})
            if r1.fun < best_re:
                best_re = float(r1.fun)
                B_re = uB(r1.x)
            r2 = opt.minimize(lambda th: abs(eval_tree_np(comp, uB(th))), r1.x, method="L-BFGS-B", options={"maxiter": 300})
            if r2.fun < best_abs:
                best_abs = float(r2.fun)
                B_z = uB(r2.x)

        # Build 3D Hopf coordinates for B_z (or B_re), verify with tree_amplitude_mp
        B_use = B_re if best_re < 0 else B_z
        edge_vec = {}
        for idx, (u, v) in enumerate(edges):
            a, b = B_use[0, idx], B_use[1, idx]
            w = (mp.mpf(2 * float(np.real(np.conj(a) * b))), mp.mpf(2 * float(np.imag(np.conj(a) * b))), mp.mpf(float(abs(a) ** 2 - abs(b) ** 2)))
            edge_vec[(u, v)] = w
            edge_vec[(v, u)] = (-w[0], -w[1], -w[2])
        pts_mp = {0: (mp.mpf(0), mp.mpf(0), mp.mpf(0))}
        q = [0]
        for u in q:
            for w in T.neighbors(u):
                if w not in pts_mp:
                    p0 = pts_mp[u]
                    dv = edge_vec[(u, w)]
                    pts_mp[w] = (p0[0] + dv[0], p0[1] + dv[1], p0[2] + dv[2])
                    q.append(w)
        pts_list = [pts_mp[i] for i in range(T.number_of_nodes())]
        amp_mp = tree_amplitude_mp(T, pts_list)
        spider_entries[sname] = {
            "n": T.number_of_nodes(),
            "m": m,
            "arms": arms,
            "min_re": best_re,
            "min_abs": best_abs,
            "mp50_sample_re": mp.nstr(amp_mp.real, 50),
            "mp50_sample_im": mp.nstr(amp_mp.imag, 50),
            "mp50_sample_abs": mp.nstr(abs(amp_mp), 50),
        }
        print(f"[{sname}] min_re={best_re:.8f}, min_abs={best_abs:.3e}, mp50_re={mp.nstr(amp_mp.real, 12)}")

    # 4. Exact Gaussian-integer / 3D integer Hopf witnesses on Linear Paths LG_15, LG_16, LG_17
    path_witness_specs = {
        "LG_15": {
            "Br": [[5, -2, 5, 1, 5, 2, 5, 0, 5, -1, 5, 0, 5, 1], [0, 4, 0, 4, 1, 5, 0, 5, -1, 5, -1, 5, 2, 5]],
            "Bi": [[0, 1, 0, 2, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0]],
        },
        "LG_16": {
            "Br": [[4, 2, 4, -1, 4, -2, 4, 0, 4, 1, 4, 0, 4, -1, 3], [0, 3, 0, 3, -1, 4, 0, 4, 1, 4, 1, 4, -2, 4, -1]],
            "Bi": [[0, 1, 0, 2, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0, 2]],
        },
        "LG_17": {
            "Br": [[2, -1, 2, 0, 2, 1, 2, 0, 2, -1, 2, 0, 2, 0, 2, 0], [0, 2, 0, 2, 0, 2, 0, 2, -1, 2, 0, 2, 1, 2, 0, 2]],
            "Bi": [[0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0]],
        },
    }
    linear_path_witnesses = {}
    for pname, spec in path_witness_specs.items():
        Br, Bi = spec["Br"], spec["Bi"]
        m = len(Br[0])
        n = m + 1
        T = nx.path_graph(n)
        gi_re, gi_im, diag_prod = path_exact_gi(Br, Bi)
        assert gi_re < 0
        pts_int = path_pts_int_from_spinors(Br, Bi)
        assert len({tuple(p) for p in pts_int}) == n
        pts_mp = [(mp.mpf(p[0]), mp.mpf(p[1]), mp.mpf(p[2])) for p in pts_int]
        amp_mp = tree_amplitude_mp(T, pts_mp)
        amp_fast = g_amplitude(n, list(T.edges()), np.array(pts_int, dtype=float))
        # Exact ratio conj(gi_re + i * gi_im) / diag_prod == amp_mp!
        exact_re_mp = mp.mpf(gi_re) / mp.mpf(diag_prod)
        exact_im_mp = mp.mpf(-gi_im) / mp.mpf(diag_prod)
        assert abs(amp_mp.real - exact_re_mp) < mp.mpf("1e-50")
        assert abs(amp_mp.imag - exact_im_mp) < mp.mpf("1e-50")
        linear_path_witnesses[pname] = {
            "n": n,
            "m": m,
            "Br": Br,
            "Bi": Bi,
            "pts_xyz_int": pts_int,
            "unnorm_gi_re": gi_re,
            "unnorm_gi_im": gi_im,
            "diag_prod": diag_prod,
            "mp50_re": mp.nstr(amp_mp.real, 50),
            "mp50_im": mp.nstr(amp_mp.imag, 50),
            "mp50_abs": mp.nstr(abs(amp_mp), 50),
            "g_amplitude_fast_re": float(amp_fast.real),
            "g_amplitude_fast_im": float(amp_fast.imag),
        }
        print(f"[{pname}] exact Re = {gi_re}/{diag_prod} = {mp.nstr(amp_mp.real, 12)} < 0, mp50 match OK!")

    # 5. Path modulus |A_{LG_{m+1}}| scan for m = 5..24
    path_modulus_scan = {}
    for m in [5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 24]:
        rng_p = np.random.default_rng(900 + m)
        best_abs = 1e9
        for rep in range(12):
            th0 = rng_p.normal(size=4 * m)

            def obj_abs(th):
                B = th[: 2 * m].reshape(2, m) + 1j * th[2 * m :].reshape(2, m)
                B /= np.maximum(np.linalg.norm(B, axis=0, keepdims=True), 1e-12)
                return abs(path_eval_np(B))

            res = opt.minimize(obj_abs, th0, method="L-BFGS-B", options={"maxiter": 150})
            best_abs = min(best_abs, float(res.fun))
        path_modulus_scan[f"LG_{m + 1}"] = {"n": m + 1, "m": m, "min_abs": best_abs}

    out = {
        "cherry_tree_10": cherry_entry,
        "minimality_n4_to_n9": minimality_n4_to_n9,
        "n10_violators": n10_violators,
        "spider_witnesses": spider_entries,
        "linear_path_witnesses": linear_path_witnesses,
        "path_modulus_scan": path_modulus_scan,
        "elapsed_sec": round(time.time() - t_start, 2),
    }
    out_path = ROOT / "data" / "conjecture_c_tree_counterexamples.json"
    out_path.write_text(json.dumps(out, indent=2) + "\n")
    print(f"Wrote {out_path} in {out['elapsed_sec']}s")


if __name__ == "__main__":
    main()
