"""Tight-cluster minimality search (n=6, 7), triangle-free & bipartite n=8 tests, and integer witnesses."""
from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
import json
import math
from pathlib import Path
import sys
import time

import mpmath as mp
import networkx as nx
import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from scripts.scan_malkoun import canonical_edges, g_amplitude, g_amplitude_mp  # noqa: E402
from scripts.scan_minimality_and_connectivity import (  # noqa: E402
    _graph_invariants,
    _is_well_separated,
    _pair_metrics,
    _verify_mp50_row,
)


def _cluster_starts(
    n_verts: int, dim: int, count: int, rng: np.random.Generator
) -> list[np.ndarray]:
    """Generate tight dipole, 3-cluster, multiscale, and wide starts matching small-gap minima."""
    starts: list[np.ndarray] = []
    for k in range(count):
        mode = k % 4
        if mode == 0:
            # 2-vertex dipole inside O(1..5) background
            pts = rng.normal(scale=float(10.0 ** rng.uniform(0.0, 0.9)), size=(n_verts, dim))
            i, j = rng.choice(n_verts, size=2, replace=False)
            eps = float(10.0 ** rng.uniform(-3.6, -1.4))
            delta = rng.normal(size=dim)
            delta = delta / max(1e-12, float(np.linalg.norm(delta))) * eps
            pts[j] = pts[i] + delta
        elif mode == 1:
            # 3-vertex tight cluster inside O(1..8) background (mimics K4_2e_K3_2conn_n7)
            pts = rng.normal(scale=float(10.0 ** rng.uniform(0.1, 1.0)), size=(n_verts, dim))
            tri = rng.choice(n_verts, size=3, replace=False)
            anchor = pts[tri[0]].copy()
            eps = float(10.0 ** rng.uniform(-3.6, -1.5))
            pts[tri[1]] = anchor + rng.normal(scale=eps, size=dim)
            pts[tri[2]] = anchor + rng.normal(scale=eps * 1.4, size=dim)
        elif mode == 2:
            # Extreme multiscale log-uniform
            scales = 10.0 ** rng.uniform(-2.5, 2.5, size=(n_verts - 1, 1))
            pts = np.vstack([np.zeros((1, dim)), rng.normal(size=(n_verts - 1, dim)) * scales])
        else:
            # Near-collinear with tiny transverse gaps and hierarchical x
            xs = np.exp(rng.uniform(-2.5, 2.5, size=n_verts)) * rng.choice([-1.0, 1.0], size=n_verts)
            pts = np.zeros((n_verts, dim), dtype=np.float64)
            pts[:, 0] = xs[rng.permutation(n_verts)]
            pts[:, 1:] = rng.normal(scale=float(10.0 ** rng.uniform(-2.5, -0.3)), size=(n_verts, dim - 1))
        pts = pts - pts[0:1]
        starts.append(pts[1:].ravel())
    return starts


def _cluster_scan_graph(task: tuple) -> dict:
    """Optimize 2D (and optionally 3D) amplitude with tight-cluster starts."""
    name, n_verts, edges, n_starts_2d, n_starts_3d, maxiter, seed, early_stop = task
    edges_c = canonical_edges(edges)
    inv = _graph_invariants(n_verts, edges_c)

    p_col = np.array([[float(i), 0.0, 0.0] for i in range(n_verts)], dtype=np.float64)
    col_val = g_amplitude(n_verts, edges_c, p_col)
    scale = max(1.0, abs(col_val)) if np.isfinite(col_val.real) else 1.0
    rng = np.random.default_rng(seed)

    def unpack_2d(theta: np.ndarray) -> np.ndarray:
        pts = np.zeros((n_verts, 3), dtype=np.float64)
        pts[1:, :2] = theta.reshape(n_verts - 1, 2)
        return pts

    def unpack_3d(theta: np.ndarray) -> np.ndarray:
        pts = np.zeros((n_verts, 3), dtype=np.float64)
        pts[1:, :] = theta.reshape(n_verts - 1, 3)
        return pts

    def eval_safe(pts: np.ndarray) -> complex | None:
        min_e, min_all, diam = _pair_metrics(pts, edges_c)
        if min_e < 1e-5 or (min_all / max(diam, 1e-12)) < 1e-6:
            return None
        val = g_amplitude(n_verts, edges_c, pts)
        if not (math.isfinite(val.real) and math.isfinite(val.imag)):
            return None
        return val

    def obj_2d_re(theta: np.ndarray) -> float:
        v = eval_safe(unpack_2d(theta))
        return 1e9 if v is None else float(v.real / scale)

    def obj_3d_re(theta: np.ndarray) -> float:
        v = eval_safe(unpack_3d(theta))
        return 1e9 if v is None else float(v.real / scale)

    def obj_3d_abs(theta: np.ndarray) -> float:
        v = eval_safe(unpack_3d(theta))
        return 1e9 if v is None else float(abs(v) / scale)

    best_2d_re = float("inf")
    best_2d_pts = None
    best_2d_sep = (0.0, 0.0, 0.0)
    for x0 in _cluster_starts(n_verts, 2, n_starts_2d, rng):
        res = minimize(obj_2d_re, x0, method="BFGS", options={"maxiter": maxiter, "gtol": 1e-4})
        pts = unpack_2d(res.x)
        min_e, min_all, diam = _pair_metrics(pts, edges_c)
        if min_e <= 1e-5 or (min_all / max(diam, 1e-12)) <= 1e-6 or not np.all(np.isfinite(pts)):
            continue
        val = g_amplitude(n_verts, edges_c, pts)
        if math.isfinite(val.real) and val.real < best_2d_re:
            best_2d_re = float(val.real)
            best_2d_pts = pts.tolist()
            best_2d_sep = (min_e, min_all, diam)
        if early_stop and best_2d_re < -1e-2:
            break

    best_3d_re = float("inf")
    best_3d_re_pts = None
    best_3d_abs = float("inf")
    best_3d_abs_pts = None
    if n_starts_3d > 0:
        for x0 in _cluster_starts(n_verts, 3, n_starts_3d, rng):
            r1 = minimize(obj_3d_re, x0, method="BFGS", options={"maxiter": maxiter, "gtol": 1e-4})
            pts1 = unpack_3d(r1.x)
            me1, ma1, d1 = _pair_metrics(pts1, edges_c)
            if me1 > 1e-5 and (ma1 / max(d1, 1e-12)) > 1e-6 and np.all(np.isfinite(pts1)):
                v1 = g_amplitude(n_verts, edges_c, pts1)
                if math.isfinite(v1.real) and v1.real < best_3d_re:
                    best_3d_re = float(v1.real)
                    best_3d_re_pts = pts1.tolist()

            r2 = minimize(obj_3d_abs, x0, method="BFGS", options={"maxiter": maxiter, "gtol": 1e-4})
            pts2 = unpack_3d(r2.x)
            me2, ma2, d2 = _pair_metrics(pts2, edges_c)
            if me2 > 1e-5 and (ma2 / max(d2, 1e-12)) > 1e-6 and np.all(np.isfinite(pts2)):
                v2 = g_amplitude(n_verts, edges_c, pts2)
                av2 = abs(v2)
                if math.isfinite(av2) and av2 < best_3d_abs:
                    best_3d_abs = float(av2)
                    best_3d_abs_pts = pts2.tolist()
            if early_stop and best_3d_abs < 0.5 and best_3d_re < -1e-2:
                break

    violates = min(best_2d_re, best_3d_re, best_3d_abs) < 0.999
    return {
        "name": name,
        "collinear_val": float(col_val.real),
        "scale": float(scale),
        **inv,
        "min_2d_re": best_2d_re,
        "min_3d_re": best_3d_re,
        "min_3d_abs": best_3d_abs,
        "min_edge_dist_2d": best_2d_sep[0],
        "min_all_dist_2d": best_2d_sep[1],
        "diameter_2d": best_2d_sep[2],
        "best_2d_pts": best_2d_pts,
        "best_3d_re_pts": best_3d_re_pts,
        "best_3d_abs_pts": best_3d_abs_pts,
        "violates": bool(violates),
    }


def _widen_aspect_ratio_2d(
    n_verts: int, edges_c: list[tuple[int, int]], pts_init: np.ndarray
) -> np.ndarray:
    """Widen min_all_dist / diam while staying inside {Re(A_G) < -0.5}."""
    cur = np.asarray(pts_init, dtype=np.float64).copy()
    cur[:, 2] = 0.0
    cur = cur - cur[0:1]

    def ratio_obj(theta: np.ndarray) -> float:
        pts = np.zeros((n_verts, 3), dtype=np.float64)
        pts[1:, :2] = theta.reshape(n_verts - 1, 2)
        min_e, min_all, diam = _pair_metrics(pts, edges_c)
        if min_e < 1e-6:
            return 1e12
        val = g_amplitude(n_verts, edges_c, pts)
        if not math.isfinite(val.real) or val.real > -0.25:
            return 1e8 + max(0.0, float(val.real) + 0.25) * 1e4
        return float(diam / max(min_all, 1e-12))

    x0 = cur[1:, :2].ravel()
    res = minimize(ratio_obj, x0, method="Nelder-Mead", options={"maxiter": 600})
    cand = np.zeros((n_verts, 3), dtype=np.float64)
    cand[1:, :2] = res.x.reshape(n_verts - 1, 2)
    vc = g_amplitude(n_verts, edges_c, cand)
    _, ma_c, dm_c = _pair_metrics(cand, edges_c)
    _, ma_0, dm_0 = _pair_metrics(cur, edges_c)
    if math.isfinite(vc.real) and vc.real < -0.25 and (ma_c / dm_c) > (ma_0 / dm_0):
        return cand
    return cur


def _construct_integer_witness(row: dict) -> dict | None:
    """Construct verified integer planar configuration with distinct x-coordinates and IVT zero proof."""
    if row.get("best_2d_pts") is None or row["min_2d_re"] >= -1e-2:
        return None
    n_verts = row["n"]
    edges_c = canonical_edges(row["edges"])
    pts_wide = _widen_aspect_ratio_2d(n_verts, edges_c, np.asarray(row["best_2d_pts"], dtype=np.float64))
    pts_xy = pts_wide[:, :2]
    _, min_all, diam = _pair_metrics(pts_wide, edges_c)

    best_int = None
    best_max_coord = float("inf")
    for mult in (1.5, 2.0, 3.0, 5.0, 8.0, 15.0, 30.0, 60.0):
        scale = mult / max(min_all, 1e-12)
        arr = np.rint(pts_xy * scale).astype(int)
        arr = arr - np.rint(np.mean(arr, axis=0)).astype(int)
        # Ensure all vertices distinct
        if len({(int(r[0]), int(r[1])) for r in arr}) < n_verts:
            continue
        # Ensure distinct x-coordinates by minimal ±1 nudges if needed
        used_x: set[int] = set()
        for idx in range(n_verts):
            if int(arr[idx, 0]) in used_x:
                for dx in (1, -1, 2, -2, 3, -3):
                    if int(arr[idx, 0]) + dx not in used_x:
                        arr[idx, 0] += dx
                        break
            used_x.add(int(arr[idx, 0]))
        if len({int(r[0]) for r in arr}) < n_verts:
            continue

        pts3 = np.column_stack([arr.astype(float), np.zeros(n_verts)])
        v = g_amplitude(n_verts, edges_c, pts3)
        if math.isfinite(v.real) and v.real < -1e-2:
            # Shrink coordinates greedily toward smaller integers
            cur = arr.copy()
            for _ in range(30):
                changed = False
                for i in range(n_verts):
                    for d in (0, 1):
                        if abs(cur[i, d]) <= 1:
                            continue
                        for factor in (0.5, 0.75, 0.9):
                            cand = cur.copy()
                            cand[i, d] = int(round(cand[i, d] * factor))
                            if len({int(r[0]) for r in cand}) < n_verts:
                                continue
                            pc = np.column_stack([cand.astype(float), np.zeros(n_verts)])
                            me, ma, _ = _pair_metrics(pc, edges_c)
                            if ma >= 1.0 and me >= 1.0:
                                vc = g_amplitude(n_verts, edges_c, pc)
                                if math.isfinite(vc.real) and vc.real < -1e-2:
                                    cur = cand
                                    changed = True
                                    break
                        if changed:
                            break
                if not changed:
                    break
            max_c = int(np.max(np.abs(cur)))
            if max_c < best_max_coord:
                best_max_coord = max_c
                best_int = cur
            break

    if best_int is None:
        return None

    pts_neg = [[float(r[0]), float(r[1]), 0.0] for r in best_int]
    pts_col = [[float(r[0]), 0.0, 0.0] for r in best_int]
    f_neg = g_amplitude(n_verts, edges_c, np.asarray(pts_neg))
    mp_neg = g_amplitude_mp(n_verts, edges_c, pts_neg, dps=50)
    mp_col = g_amplitude_mp(n_verts, edges_c, pts_col, dps=50)
    rel_err = abs(f_neg.real - float(mp_neg.real)) / max(1.0, abs(float(mp_neg.real)))
    verified = (
        rel_err < 1e-10
        and abs(float(mp_neg.imag)) < 1e-40
        and abs(float(mp_col.imag)) < 1e-40
        and float(mp_neg.real) < -1e-2
        and float(mp_col.real) >= 1.0
        and len({int(r[0]) for r in best_int}) == n_verts
    )
    return {
        "name": row["name"],
        "n": n_verts,
        "m": row["m"],
        "node_connectivity": row["node_connectivity"],
        "is_planar": row["is_planar"],
        "is_regular": row["is_regular"],
        "is_triangle_free": row.get("girth", 3) >= 4 if "girth" in row else None,
        "edges": edges_c,
        "pts_xy_int": [[int(r[0]), int(r[1])] for r in best_int],
        "max_abs_coord": int(best_max_coord),
        "widened_ratio": float(_pair_metrics(pts_wide, edges_c)[1] / _pair_metrics(pts_wide, edges_c)[2]),
        "mp50_t1_re": mp.nstr(mp_neg.real, 40),
        "mp50_t1_im": mp.nstr(mp_neg.imag, 15),
        "mp50_t0_col_re": mp.nstr(mp_col.real, 30),
        "rel_err_float_vs_mp50": rel_err,
        "verified_mp50": bool(verified),
    }


def run_all(workers: int = 12) -> dict:
    t_start = time.monotonic()
    atlas = nx.graph_atlas_g()

    # --- Stage 1: Tight-cluster stress test on all 112 connected n=6 graphs ---
    t0 = time.monotonic()
    conn6 = [g for g in atlas if g.number_of_nodes() == 6 and nx.is_connected(g)]
    tasks6 = [
        (f"tc_n6_{i}_m{g.number_of_edges()}", 6, list(g.edges()), 12, 4, 60, 70000 + i, True)
        for i, g in enumerate(conn6)
    ]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        res6 = list(pool.map(_cluster_scan_graph, tasks6))
    dt6 = round(time.monotonic() - t0, 2)
    viol6 = [r for r in res6 if r["violates"]]
    print(
        f"[Stage 1: n=6 tight-cluster] {len(res6)} graphs in {dt6}s | "
        f"min_2d_re={min(r['min_2d_re'] for r in res6):.6f}, "
        f"min_3d_re={min(r['min_3d_re'] for r in res6):.6f}, "
        f"min_3d_abs={min(r['min_3d_abs'] for r in res6):.6f} | violations={len(viol6)}"
    )

    # --- Stage 2: Edge-minimality on n=7 (all 445 non-bipartite m<=11 + subgraphs + K4_v_K4) ---
    t0 = time.monotonic()
    nb7 = [
        g
        for g in atlas
        if g.number_of_nodes() == 7
        and nx.is_connected(g)
        and g.number_of_edges() <= 11
        and not nx.is_bipartite(g)
    ]
    # All non-isomorphic connected edge-deletions of K4_2e_K3_2conn_n7 are in nb7, plus add K4_v_K4(m=12)
    tasks7 = [
        (f"tc_n7_{i}_m{g.number_of_edges()}_k{nx.node_connectivity(g)}", 7, list(g.edges()), 10, 0, 55, 80000 + i, True)
        for i, g in enumerate(nb7)
    ]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        res7 = list(pool.map(_cluster_scan_graph, tasks7))
    dt7 = round(time.monotonic() - t0, 2)
    viol7 = [r for r in res7 if r["violates"]]
    print(
        f"[Stage 2: n=7 non-bipartite m<=11] {len(res7)} graphs in {dt7}s | "
        f"min_2d_re={min(r['min_2d_re'] for r in res7):.6f} | violations={len(viol7)}"
    )
    for r in sorted(viol7, key=lambda x: (x["m"], x["min_2d_re"])):
        r["mp50_checks"] = _verify_mp50_row(r)
        r["verified_mp50"] = bool(r["mp50_checks"]) and all(c["ok"] for c in r["mp50_checks"].values())
        print(
            f"  [n=7 VIOL] {r['name']:24s} m={r['m']:2d} kappa={r['node_connectivity']} "
            f"planar={r['is_planar']} | 2d_re={r['min_2d_re']:.6f} mp50={r['verified_mp50']}"
        )

    # --- Stage 3: Triangle-free & bipartite n=8 stress test ---
    t0 = time.monotonic()
    stage3_defs = [
        ("Wagner_M8", 8, [(i, (i + 1) % 8) for i in range(8)] + [(i, i + 4) for i in range(4)]),
        ("C5_chord_triFree_2conn_n8", 8, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (3, 5), (5, 6), (6, 7), (7, 4), (1, 6)]),
        ("C5_b_C5_triFree_n8", 8, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (3, 5), (5, 6), (6, 7), (7, 4)]),
        ("Q3_cube", 8, list(nx.convert_node_labels_to_integers(nx.cubical_graph()).edges())),
        ("K4_4_bip", 8, list(nx.complete_bipartite_graph(4, 4).edges())),
        ("K3_5_bip", 8, list(nx.complete_bipartite_graph(3, 5).edges())),
        ("C4_eq_C4_2conn", 8, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4), (3, 4), (2, 5)]),
    ]
    # Record girth to prove triangle-freeness accurately
    girths = {}
    for nm, nv, ed in stage3_defs:
        G = nx.Graph(ed)
        G.add_nodes_from(range(nv))
        girths[nm] = nx.girth(G)
    tasks3 = [(nm, nv, ed, 24, 10, 120, 90000 + i, False) for i, (nm, nv, ed) in enumerate(stage3_defs)]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        res3 = list(pool.map(_cluster_scan_graph, tasks3))
    dt3 = round(time.monotonic() - t0, 2)
    print(f"[Stage 3: n=8 triangle-free & bipartite] {len(res3)} graphs in {dt3}s")
    for r in res3:
        r["girth"] = girths[r["name"]]
        if r["violates"]:
            r["mp50_checks"] = _verify_mp50_row(r)
            r["verified_mp50"] = bool(r["mp50_checks"]) and all(c["ok"] for c in r["mp50_checks"].values())
        print(
            f"  {r['name']:26s} m={r['m']:2d} k={r['node_connectivity']} girth={r['girth']} "
            f"bip={str(r['is_bipartite'])[0]} | 2d_re={r['min_2d_re']:13.4f} "
            f"3d_re={r['min_3d_re']:13.4f} 3d_abs={r['min_3d_abs']:12.4f} | "
            f"viol={r['violates']} mp50={r.get('verified_mp50')}"
        )

    # --- Stage 4: Verified small-integer planar witnesses ---
    t0 = time.monotonic()
    prev_data = json.loads((ROOT / "data" / "minimality_and_connectivity_scan.json").read_text(encoding="utf-8"))
    headline_rows = []
    # Collect n=7 smallest violations + previous n=7 + key n=8 witnesses
    seen_names = set()
    for r in sorted(viol7, key=lambda x: (x["m"], x["min_2d_re"])):
        r["girth"] = nx.girth(nx.Graph(r["edges"]))
        headline_rows.append(r)
        seen_names.add(r["name"])
    for r in prev_data["stage_b_n7_pass2_deep"]["violations"]:
        if r["name"] not in seen_names:
            r["girth"] = nx.girth(nx.Graph(r["edges"]))
            headline_rows.append(r)
            seen_names.add(r["name"])
    for r in res3:
        if r["violates"] and r.get("best_2d_pts") is not None and r["min_2d_re"] < 0:
            headline_rows.append(r)
            seen_names.add(r["name"])
    for nm in ("K4_eq_K4_2conn", "K4_3e_3conn", "K4xK2_4reg_4conn", "antiprism_4"):
        for r in prev_data["stage_c_n8_taxonomy"]["rows"]:
            if r["name"] == nm and nm not in seen_names:
                r["girth"] = nx.girth(nx.Graph(r["edges"]))
                headline_rows.append(r)
                seen_names.add(nm)

    integer_witnesses = []
    for row in headline_rows:
        w = _construct_integer_witness(row)
        if w is not None:
            integer_witnesses.append(w)
            print(
                f"  [INT WITNESS] {w['name']:22s} n={w['n']} m={w['m']} k={w['node_connectivity']} "
                f"max|c|={w['max_abs_coord']} | t0={w['mp50_t0_col_re'][:14]} t1={w['mp50_t1_re'][:18]} "
                f"mp50={w['verified_mp50']}"
            )
    dt4 = round(time.monotonic() - t0, 2)

    # Verify any viol6
    for r in viol6:
        r["mp50_checks"] = _verify_mp50_row(r)
        r["verified_mp50"] = bool(r["mp50_checks"]) and all(c["ok"] for c in r["mp50_checks"].values())

    def _compact(row: dict) -> dict:
        if row["violates"]:
            return row
        out = dict(row)
        out.pop("best_2d_pts", None)
        out.pop("best_3d_re_pts", None)
        out.pop("best_3d_abs_pts", None)
        return out

    return {
        "total_duration_sec": round(time.monotonic() - t_start, 2),
        "stage_1_n6": {
            "count": len(res6),
            "duration_sec": dt6,
            "min_2d_re": min(r["min_2d_re"] for r in res6),
            "min_3d_re": min(r["min_3d_re"] for r in res6),
            "min_3d_abs": min(r["min_3d_abs"] for r in res6),
            "violations": [_compact(r) for r in viol6],
            "top_10": sorted([_compact(r) for r in res6], key=lambda x: min(x["min_2d_re"], x["min_3d_re"], x["min_3d_abs"]))[:10],
        },
        "stage_2_n7_nonbip_le11": {
            "count": len(res7),
            "duration_sec": dt7,
            "min_2d_re": min(r["min_2d_re"] for r in res7),
            "violations": [_compact(r) for r in sorted(viol7, key=lambda x: (x["m"], x["min_2d_re"]))],
            "top_15_lowest": sorted([_compact(r) for r in res7], key=lambda x: x["min_2d_re"])[:15],
        },
        "stage_3_n8_trifree_bip": {
            "count": len(res3),
            "duration_sec": dt3,
            "rows": res3,
        },
        "stage_4_integer_witnesses": {
            "duration_sec": dt4,
            "witnesses": integer_witnesses,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument("--output", type=Path, default=ROOT / "data" / "deep_minimality_and_witnesses.json")
    args = parser.parse_args()
    out = run_all(workers=args.workers)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"Wrote {args.output} in {out['total_duration_sec']}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
