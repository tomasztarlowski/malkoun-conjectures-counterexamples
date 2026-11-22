"""Exact rational, symbolic, and Gaussian-integer analysis of barbell_K4_8 counterexample."""
from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import sys
import time

import mpmath as mp
import networkx as nx
import numpy as np
from scipy.optimize import minimize
import sympy as sp

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from scripts.scan_malkoun import canonical_edges, g_amplitude, g_amplitude_mp  # noqa: E402

BARBELL_EDGES = canonical_edges(
    list(nx.complete_graph(4).edges())
    + [(3, 4)]
    + [(u + 4, v + 4) for u, v in nx.complete_graph(4).edges()]
)


def exact_gaussian_amplitude(
    n_verts: int, edges: list[tuple[int, int]], pts_xy: list[tuple[int, int]]
) -> dict:
    """Compute A_G exactly in Q(i) whenever all pairwise edge lengths are exact integers."""
    edges_c = canonical_edges(edges)
    nbrs: dict[int, list[int]] = {v: [] for v in range(n_verts)}
    lengths: dict[tuple[int, int], int] = {}
    psi_int: dict[tuple[int, int], tuple[complex, complex]] = {}

    for u, w in edges_c:
        dx = pts_xy[w][0] - pts_xy[u][0]
        dy = pts_xy[w][1] - pts_xy[u][1]
        d2 = dx * dx + dy * dy
        r = math.isqrt(d2)
        if r * r != d2 or r == 0:
            raise ValueError(f"Edge ({u},{w}) length^2={d2} is not a nonzero perfect square")
        lengths[(u, w)] = r
        lengths[(w, u)] = r
        # Unnormalized exact Gaussian integer spinor: (r, dx + i*dy)
        psi_int[(u, w)] = (r + 0j, complex(dx, dy))  # will re-run with exact Python ints below
        nbrs[u].append(w)
        nbrs[w].append(u)

    # Pure Python arbitrary-precision Gaussian integers as (re: int, im: int)
    def g_add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
        return (a[0] + b[0], a[1] + b[1])

    def g_sub(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
        return (a[0] - b[0], a[1] - b[1])

    def g_mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    def g_omega(p: tuple[tuple[int, int], tuple[int, int]], q: tuple[tuple[int, int], tuple[int, int]]) -> tuple[int, int]:
        return g_sub(g_mul(p[0], q[1]), g_mul(p[1], q[0]))

    psi_gi: dict[tuple[int, int], tuple[tuple[int, int], tuple[int, int]]] = {}
    for u, w in edges_c:
        dx = pts_xy[w][0] - pts_xy[u][0]
        dy = pts_xy[w][1] - pts_xy[u][1]
        r = lengths[(u, w)]
        psi_gi[(u, w)] = ((r, 0), (dx, dy))
        psi_gi[(w, u)] = ((r, 0), (-dx, -dy))

    # Denominator = prod_{(u,w) in edges_c} omega(psi_{u,w}, psi_{w,u})
    denom = (1, 0)
    for u, w in edges_c:
        denom = g_mul(denom, g_omega(psi_gi[(u, w)], psi_gi[(w, u)]))

    # Bridge factorization across (3, 4) for barbell_K4_8 or general tensor contraction over Z[i]!
    slot: dict[tuple[int, int], int] = {}
    cnt = 0
    for u, w in edges_c:
        slot[(u, w)] = cnt
        cnt += 1
        slot[(w, u)] = cnt
        cnt += 1

    active: list[tuple[list[int], dict[tuple[int, ...], tuple[int, int]]]] = []
    for v in range(n_verts):
        ns = nbrs[v]
        deg = len(ns)
        tens: dict[tuple[int, ...], tuple[int, int]] = {}
        for perm in itertools.permutations(ns):
            vecs = [psi_gi[(v, ww)] for ww in perm]
            for bits in itertools.product((0, 1), repeat=deg):
                prod = (1, 0)
                for vec, b in zip(vecs, bits):
                    prod = g_mul(prod, vec[b])
                prev = tens.get(bits, (0, 0))
                tens[bits] = g_add(prev, prod)
        tens = {k: val for k, val in tens.items() if val != (0, 0)}
        active.append(([slot[(v, ww)] for ww in ns], tens))

    # Contract edges greedily (no shared-pair blowup)
    for u, w in edges_c:
        su, sw = slot[(u, w)], slot[(w, u)]
        iu = next(idx for idx, (lbls, _) in enumerate(active) if su in lbls)
        iw = next(idx for idx, (lbls, _) in enumerate(active) if sw in lbls)
        if iu == iw:
            lu, tu = active[iu]
            pu, pw = lu.index(su), lu.index(sw)
            rem = [x for x in lu if x not in (su, sw)]
            tnew: dict[tuple[int, ...], tuple[int, int]] = {}
            for kb, val in tu.items():
                bu, bw = kb[pu], kb[pw]
                if bu == bw:
                    continue
                rkey = tuple(kb[k] for k in range(len(lu)) if k not in (pu, pw))
                cur = tnew.get(rkey, (0, 0))
                nxt = g_add(cur, val) if (bu == 0 and bw == 1) else g_sub(cur, val)
                if nxt != (0, 0):
                    tnew[rkey] = nxt
                elif rkey in tnew:
                    del tnew[rkey]
            active[iu] = (rem, tnew)
        else:
            lu, tu = active[iu]
            lw, tw = active[iw]
            pu, pw = lu.index(su), lw.index(sw)
            rem_u = [x for x in lu if x != su]
            rem_w = [x for x in lw if x != sw]
            gu0: dict[tuple[int, ...], tuple[int, int]] = {}
            gu1: dict[tuple[int, ...], tuple[int, int]] = {}
            gw0: dict[tuple[int, ...], tuple[int, int]] = {}
            gw1: dict[tuple[int, ...], tuple[int, int]] = {}
            for kb, val in tu.items():
                rk = kb[:pu] + kb[pu + 1 :]
                (gu0 if kb[pu] == 0 else gu1)[rk] = val
            for kb, val in tw.items():
                rk = kb[:pw] + kb[pw + 1 :]
                (gw0 if kb[pw] == 0 else gw1)[rk] = val
            tnew = {}
            for rku in set(gu0) | set(gu1):
                u0, u1 = gu0.get(rku, (0, 0)), gu1.get(rku, (0, 0))
                for rkw in set(gw0) | set(gw1):
                    w0, w1 = gw0.get(rkw, (0, 0)), gw1.get(rkw, (0, 0))
                    val = g_sub(g_mul(u0, w1), g_mul(u1, w0))
                    if val != (0, 0):
                        tnew[rku + rkw] = val
            for idx_del in sorted((iu, iw), reverse=True):
                active.pop(idx_del)
            active.append((rem_u + rem_w, tnew))

    assert len(active) == 1 and active[0][0] == []
    num = active[0][1].get((), (0, 0))

    # Divide exact Gaussian integers: (a + bi) / (c + di) = ((ac+bd) + i(bc-ad)) / (c^2 + d^2)
    a, b = num
    c, d = denom
    norm_d = c * c + d * d
    re_frac = Fraction(a * c + b * d, norm_d)
    im_frac = Fraction(b * c - a * d, norm_d)
    return {
        "edge_lengths": {f"{u}-{w}": lengths[(u, w)] for u, w in edges_c},
        "num_gaussian": [str(a), str(b)],
        "denom_gaussian": [str(c), str(d)],
        "real_exact": f"{re_frac.numerator}/{re_frac.denominator}",
        "imag_exact": f"{im_frac.numerator}/{im_frac.denominator}",
        "real_float": float(re_frac),
        "imag_float": float(im_frac),
        "is_exact_real": im_frac == 0,
    }


def search_smallest_pythagorean() -> dict:
    """Search primitive Pythagorean families (3-4-5, 5-12-13, 8-15-17, 7-24-25) for smallest integer config with A < 0."""
    # Geometry: v3=(-1,0), v4=(1,0), v1=(-1-dx3, h), v7=(1+dx3, h),
    # v0=(-1-dx3-dx0, 0), v2=(-1-dx3-dx2, 0), v6=(1+dx3+dx0, 0), v5=(1+dx3+dx2, 0).
    # Wait: scale factor on x-gap between v3, v4 doesn't matter at all as long as x3 < x4!
    # So we can put v3=(-1,0), v4=(1,0) OR even v3=(0,0), v4=(1,0)! Keep v3=(-1,0), v4=(1,0) for symmetry.
    candidates = []
    # Also allow h up to 150, enumerating factorizations h^2 = u*v (u < v, same parity) => dx = (v-u)//2
    for h in range(4, 145, 2):
        h2 = h * h
        triples = []
        for u in range(1, h):
            if h2 % u == 0:
                v = h2 // u
                if (v - u) % 2 == 0:
                    dx = (v - u) // 2
                    r = (v + u) // 2
                    triples.append((dx, r))
        triples.sort()
        cand3 = [(dx, r) for dx, r in triples if 0.12 * h <= dx <= 0.65 * h]
        if not cand3 or len(triples) < 3:
            continue
        # Test top few large dx pairs
        big = triples[-5:]
        for dx3, r3 in cand3:
            for i in range(len(big)):
                for j in range(i + 1, len(big)):
                    dx0, r0 = big[i]
                    dx2, r2 = big[j]
                    if dx0 in (dx3,) or dx2 in (dx3,):
                        continue
                    pts = np.array(
                        [
                            [-1 - dx3 - dx0, 0, 0],
                            [-1 - dx3, h, 0],
                            [-1 - dx3 - dx2, 0, 0],
                            [-1, 0, 0],
                            [1, 0, 0],
                            [1 + dx3 + dx2, 0, 0],
                            [1 + dx3 + dx0, 0, 0],
                            [1 + dx3, h, 0],
                        ],
                        dtype=float,
                    )
                    val = g_amplitude(8, BARBELL_EDGES, pts).real
                    if val < -1.0:
                        max_coord = max(abs(-1 - dx3 - dx2), h)
                        candidates.append(
                            {
                                "max_coord": int(max_coord),
                                "h": h,
                                "dx3": dx3,
                                "r3": r3,
                                "dx0": dx0,
                                "r0": r0,
                                "dx2": dx2,
                                "r2": r2,
                                "amp_float": float(val),
                                "pts_xy": [[int(c) for c in row[:2]] for row in pts],
                            }
                        )
    candidates.sort(key=lambda c: (c["max_coord"], c["h"]))
    return {"total_found": len(candidates), "smallest": candidates[:5]}


def derive_limiting_formula() -> dict:
    """Derive exact closed-form sympy expression for lim_{eps->0+} A(barbell_K4_8) in tilt parameter u = e^{i phi}."""
    # Along the limiting configuration:
    # Left K4: v0=(-L^2,0), v2=(-L,0) with L->inf, v3=(-1,0), v1=(-1 + eps*cos(phi), eps*sin(phi))
    # Right K4: v4=(1,0), v7=(1 - eps*cos(phi), eps*sin(phi)), v6=(L^2,0), v5=(L,0)
    # Wait: let's match our exact orientation!
    # In our geometry: x2 < x0 < x1 < x3 < x4 < x7 < x6 < x5 (or x2 < x0 < -1 < 1 < x6 < x5 with v1 above v3 at angle theta from +x axis)!
    # Let u = e^{i theta} be the unit direction v_{3,1} = (cos theta, sin theta) in C,
    # Wait: in our symmetric reflection x -> -x, y -> +y:
    # v_{3,1} = u  ==>  v_{4,7} = -conj(u) = -1/u  (same y>0, opposite x!)
    # Let's check:
    # Left K4 directions (u_ij for i -> j, with u_{ji} = -u_{ij}):
    # 0->2: -1 (since x2 < x0)
    # 0->3: +1 (since x0 < x3)
    # 2->3: +1
    # 0->1: +1 (since x0 << x1!)
    # 2->1: +1 (since x2 << x1!)
    # 3->1: u  (unit complex number e^{i theta})
    # Bridge:
    # 3->4: +1
    # Right K4 directions (mirror x -> -x, y -> +y: if dx -> -dx, dy -> +dy then z -> -conj(z) = -1/z!):
    # 4->5: +1, 4->6: +1, 6->5: +1
    # 7->5: +1, 7->6: +1
    # 4->7: -1/u  (check: if 3->1 is (-dx3, h), then dx<0 => Re(u)<0, Im(u)>0; 4->7 is (+dx3, h) => Re>0, Im>0 => -conj(u) = -1/u!)
    u = sp.Symbol("u", nonzero=True)
    # Unnormalized spinor (1, w) for direction w (and (1, -w) for opposite -w)
    dir_map = {
        (0, 2): sp.Integer(-1),
        (0, 3): sp.Integer(1),
        (2, 3): sp.Integer(1),
        (0, 1): sp.Integer(1),
        (2, 1): sp.Integer(1),
        (3, 1): u,
        (3, 4): sp.Integer(1),
        (4, 5): sp.Integer(1),
        (4, 6): sp.Integer(1),
        (6, 5): sp.Integer(1),
        (7, 5): sp.Integer(1),
        (7, 6): sp.Integer(1),
        (4, 7): -1 / u,
    }
    for (a, b), val in list(dir_map.items()):
        dir_map[(b, a)] = -val

    # Vertex tensors for Left K4 {0,1,2,3} leaving bridge slot (3,4) open:
    # Build polynomial coeff or direct sum over 3!*3!*3!*4! = 5184 perms? Even faster:
    # Compute L_vec[b] symbolically by contracting 0,1,2 with 3!
    nbrs = {v: [] for v in range(8)}
    for a, b in BARBELL_EDGES:
        nbrs[a].append(b)
        nbrs[b].append(a)

    def sym_tensor(v: int) -> dict[tuple[int, ...], sp.Expr]:
        ns = nbrs[v]
        d = len(ns)
        vecs = [(sp.Integer(1), dir_map[(v, w)]) for w in ns]
        tens = {bits: sp.Integer(0) for bits in itertools.product((0, 1), repeat=d)}
        for perm in itertools.permutations(range(d)):
            for bits in itertools.product((0, 1), repeat=d):
                prod = sp.Integer(1)
                for p_idx, b in zip(perm, bits):
                    prod *= vecs[p_idx][b]
                tens[bits] += prod
        return {k: sp.expand(val) for k, val in tens.items()}

    # Contract Left side {0,1,2,3} into open leg (3,4)
    def contract_side(verts: list[int], side_edges: list[tuple[int, int]], open_v: int, open_nbr: int):
        slot = {}
        c = 0
        for a, b in side_edges:
            slot[(a, b)] = c; c += 1
            slot[(b, a)] = c; c += 1
        slot[(open_v, open_nbr)] = 99
        active = []
        for v in verts:
            lbls = [slot[(v, w)] for w in nbrs[v]]
            active.append((lbls, sym_tensor(v)))
        for a, b in side_edges:
            sa, sb = slot[(a, b)], slot[(b, a)]
            ia = next(i for i, (ls, _) in enumerate(active) if sa in ls)
            ib = next(i for i, (ls, _) in enumerate(active) if sb in ls)
            if ia == ib:
                la, ta = active[ia]
                pa, pb = la.index(sa), la.index(sb)
                rem = [x for x in la if x not in (sa, sb)]
                tnew = {}
                for kb, val in ta.items():
                    if kb[pa] == kb[pb]:
                        continue
                    rk = tuple(kb[k] for k in range(len(la)) if k not in (pa, pb))
                    s = 1 if (kb[pa] == 0 and kb[pb] == 1) else -1
                    tnew[rk] = sp.expand(tnew.get(rk, sp.Integer(0)) + s * val)
                active[ia] = (rem, {k: v for k, v in tnew.items() if v != 0})
            else:
                la, ta = active[ia]; lb, tb = active[ib]
                pa, pb = la.index(sa), lb.index(sb)
                ra = [x for x in la if x != sa]; rb = [x for x in lb if x != sb]
                ga0, ga1, gb0, gb1 = {}, {}, {}, {}
                for kb, val in ta.items(): (ga0 if kb[pa] == 0 else ga1)[kb[:pa] + kb[pa + 1:]] = val
                for kb, val in tb.items(): (gb0 if kb[pb] == 0 else gb1)[kb[:pb] + kb[pb + 1:]] = val
                tnew = {}
                for rka in set(ga0) | set(ga1):
                    u0, u1 = ga0.get(rka, sp.Integer(0)), ga1.get(rka, sp.Integer(0))
                    for rkb in set(gb0) | set(gb1):
                        w0, w1 = gb0.get(rkb, sp.Integer(0)), gb1.get(rkb, sp.Integer(0))
                        val = sp.expand(u0 * w1 - u1 * w0)
                        if val != 0:
                            tnew[rka + rkb] = val
                for idx_del in sorted((ia, ib), reverse=True):
                    active.pop(idx_del)
                active.append((ra + rb, tnew))
        assert len(active) == 1 and active[0][0] == [99]
        return [active[0][1].get((0,), sp.Integer(0)), active[0][1].get((1,), sp.Integer(0))]

    left_edges = [(a, b) for a, b in BARBELL_EDGES if a < 4 and b < 4]
    right_edges = [(a, b) for a, b in BARBELL_EDGES if a >= 4 and b >= 4]
    L_vec = contract_side([0, 1, 2, 3], left_edges, 3, 4)
    R_vec = contract_side([4, 5, 6, 7], right_edges, 4, 3)

    num = sp.expand(L_vec[0] * R_vec[1] - L_vec[1] * R_vec[0])
    denom = sp.Integer(1)
    for a, b in BARBELL_EDGES:
        # omega((1, dir), (1, -dir)) = -2 * dir
        denom *= (-2 * dir_map[(a, b)])
    amp_u = sp.simplify(num / denom)

    # Express in terms of c = cos(theta) = (u + 1/u)/2 (note u = -e^{-i alpha} or e^{i theta})
    theta = sp.Symbol("theta", real=True)
    amp_theta = sp.simplify(sp.re(amp_u.subs(u, sp.exp(sp.I * theta))))
    c = sp.Symbol("c", real=True)
    amp_cos = sp.simplify(amp_theta.subs(sp.cos(theta), c).subs(sp.sin(theta) ** 2, 1 - c ** 2))
    # Expand cleanly as polynomial in c = Re(u)
    poly_c = sp.Poly(sp.expand(amp_cos.trigsimp() if hasattr(amp_cos, "trigsimp") else amp_cos), c)
    # Also evaluate using cos(theta) = (u + 1/u)/2 directly
    # Substitute u + 1/u -> 2c
    c_expr = sp.simplify((amp_u + amp_u.subs(u, 1 / u)) / 2)
    expr_c = sp.expand(amp_u.subs(u, c + sp.I * sp.sqrt(1 - c ** 2)))
    expr_c = sp.simplify(sp.expand(expr_c))

    # Numeric sanity check against scan! When v3=(-1,0), v1=(-1 - dx3, h), u = (-dx3 + i h)/r => c = -dx3/r < 0
    return {
        "L_vec": [str(L_vec[0]), str(L_vec[1])],
        "R_vec": [str(R_vec[0]), str(R_vec[1])],
        "amp_of_u": str(sp.factor(amp_u)),
        "amp_of_c_where_c_is_Re_u": str(sp.factor(expr_c)),
        "amp_expanded_in_c": str(sp.expand(expr_c)),
        "roots_in_c": [str(r) for r in sp.solve(sp.Eq(expr_c, 0), c)],
        "val_at_c_minus_1": str(expr_c.subs(c, -1)),
        "val_at_c_plus_1": str(expr_c.subs(c, 1)),
        "val_at_c_minus_7_over_25": str(expr_c.subs(c, sp.Rational(-7, 25))),
    }


def _opt_n6_planar(task: tuple) -> dict:
    name, edges, seed = task
    rng = np.random.default_rng(seed)

    def obj(theta: np.ndarray) -> float:
        pts = np.hstack([np.vstack([np.zeros((1, 2)), theta.reshape(5, 2)]), np.zeros((6, 1))])
        for u, w in edges:
            if np.linalg.norm(pts[w] - pts[u]) < 1e-4:
                return 1e8
        val = g_amplitude(6, edges, pts)
        return float(val.real)

    best = 1e30
    for _ in range(8):
        r = minimize(obj, rng.normal(size=10), method="BFGS", options={"maxiter": 100})
        if r.fun < best:
            best = float(r.fun)
    return {"name": name, "m": len(edges), "edges": edges, "min_planar": best}


def scan_all_n6_planar(workers: int = 10) -> dict:
    tasks = []
    seed = 5000
    for G in nx.graph_atlas_g():
        if G.number_of_nodes() == 6 and nx.is_connected(G):
            seed += 1
            tasks.append((G.name, canonical_edges(list(G.edges())), seed))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        res = list(pool.map(_opt_n6_planar, tasks))
    res.sort(key=lambda r: r["min_planar"])
    return {
        "total_connected_n6": len(res),
        "global_min_planar": res[0]["min_planar"],
        "lowest_5": res[:5],
        "violations_below_1": [r for r in res if r["min_planar"] < 0.9999],
    }


def main() -> int:
    t0 = time.monotonic()
    pyth = search_smallest_pythagorean()
    chosen = pyth["smallest"][0]
    pts_neg = chosen["pts_xy"]
    # t=0 collinear counterpart (same x coordinates, y=0)
    pts_col = [[x, 0] for x, _ in pts_neg]

    exact_neg = exact_gaussian_amplitude(8, BARBELL_EDGES, pts_neg)
    exact_col = exact_gaussian_amplitude(8, BARBELL_EDGES, pts_col)

    mp_neg = g_amplitude_mp(8, BARBELL_EDGES, [[float(x), float(y), 0.0] for x, y in pts_neg], dps=50)
    mp.mp.dps = 50
    re_q = mp.mpf(Fraction(exact_neg["real_exact"]).numerator) / mp.mpf(Fraction(exact_neg["real_exact"]).denominator)
    diff_50 = abs(mp_neg - re_q)

    lim = derive_limiting_formula()
    n6 = scan_all_n6_planar(workers=10)

    out = {
        "duration_sec": round(time.monotonic() - t0, 2),
        "pythagorean_search": pyth,
        "chosen_config_xy": pts_neg,
        "collinear_config_xy": pts_col,
        "exact_neg_certificate": exact_neg,
        "exact_col_certificate": exact_col,
        "mp50_neg_diff": str(diff_50),
        "limiting_analytical_formula": lim,
        "all_112_connected_n6_planar": n6,
    }
    out_path = ROOT / "data" / "barbell_exact_certificate.json"
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
