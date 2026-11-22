"""Comprehensive minimality (n=6, 7) and connectivity/symmetry (n=8) scan for Malkoun arXiv:2508.13472v3."""
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

from scripts.analyze_barbell_counterexample import exact_gaussian_amplitude  # noqa: E402
from scripts.scan_malkoun import canonical_edges, g_amplitude, g_amplitude_mp  # noqa: E402


def _pair_metrics(pts: np.ndarray, edges_c: list[tuple[int, int]]) -> tuple[float, float, float]:
    """Return (min_edge_dist, min_all_dist, diameter) for an (n, 3) configuration."""
    diffs = pts[:, None, :] - pts[None, :, :]
    dists = np.linalg.norm(diffs, axis=-1)
    iu, ju = np.triu_indices(pts.shape[0], k=1)
    all_d = dists[iu, ju]
    min_all = float(np.min(all_d))
    diam = float(np.max(all_d))
    if not edges_c:
        return min_all, min_all, diam
    edge_d = [float(dists[u, v]) for u, v in edges_c]
    return float(min(edge_d)), min_all, diam


def _graph_invariants(n_verts: int, edges_c: list[tuple[int, int]]) -> dict:
    """Compute topological and symmetry invariants for metadata reporting."""
    G = nx.Graph()
    G.add_nodes_from(range(n_verts))
    G.add_edges_from(edges_c)
    degs = sorted(dict(G.degree()).values())
    is_planar, _ = nx.check_planarity(G)
    bridges = list(nx.bridges(G))
    return {
        "n": n_verts,
        "m": len(edges_c),
        "edges": edges_c,
        "deg_seq": degs,
        "is_regular": degs[0] == degs[-1] if degs else True,
        "node_connectivity": int(nx.node_connectivity(G)),
        "edge_connectivity": int(nx.edge_connectivity(G)),
        "is_biconnected": bool(nx.is_biconnected(G)),
        "is_bridgeless": len(bridges) == 0,
        "num_bridges": len(bridges),
        "is_bipartite": bool(nx.is_bipartite(G)),
        "is_planar": bool(is_planar),
        "is_tree": bool(nx.is_tree(G)),
    }


def _fiedler_split_start(
    G: nx.Graph, n_verts: int, dim: int, rng: np.random.Generator
) -> np.ndarray:
    """Place spectral clusters at separated multiscale intervals mimicking barbell bottlenecks."""
    try:
        fv = nx.fiedler_vector(G, normalized=False, method="tracemin_lu")
    except Exception:
        fv = np.linspace(-1.0, 1.0, n_verts)
    order = np.argsort(fv)
    pts = np.zeros((n_verts, dim), dtype=np.float64)
    sep = float(10.0 ** rng.uniform(0.3, 1.8))
    spread = float(10.0 ** rng.uniform(-0.8, 0.2))
    mid = n_verts // 2
    for rank, v in enumerate(order):
        side = -sep if rank < mid else sep
        local = rng.normal(scale=spread)
        pts[v, 0] = side + local
        if dim >= 2:
            pts[v, 1] = float(rng.normal(scale=spread * 0.5))
        if dim == 3:
            pts[v, 2] = float(rng.normal(scale=spread * 0.3))
    pts = pts - pts[0:1]
    return pts[1:].ravel()


def _generate_starts(
    G: nx.Graph, n_verts: int, dim: int, count: int, rng: np.random.Generator
) -> list[np.ndarray]:
    """Generate diverse initial guesses across Gaussian, multiscale, collinear, and spectral families."""
    starts: list[np.ndarray] = []
    for k in range(count):
        mode = k % 4
        if mode == 0:
            # Multiscale log-uniform coordinates per vertex
            scales = (10.0 ** rng.uniform(-1.8, 1.8, size=(n_verts - 1, 1)))
            x0 = (rng.normal(size=(n_verts - 1, dim)) * scales).ravel()
        elif mode == 1:
            # Fiedler / spectral split start
            x0 = _fiedler_split_start(G, n_verts, dim, rng)
        elif mode == 2:
            # Random-order perturbed hierarchical collinear start
            xs = np.exp(rng.uniform(-1.0, 3.2, size=n_verts - 1)) * rng.choice([-1.0, 1.0], size=n_verts - 1)
            arr = np.zeros((n_verts - 1, dim), dtype=np.float64)
            arr[:, 0] = xs[rng.permutation(n_verts - 1)]
            if dim >= 2:
                arr[:, 1:] = rng.normal(scale=0.35, size=(n_verts - 1, dim - 1))
            x0 = arr.ravel()
        else:
            x0 = rng.normal(scale=1.5, size=(n_verts - 1) * dim)
        starts.append(x0)
    return starts


def _is_well_separated(pts: np.ndarray, edges_c: list[tuple[int, int]]) -> tuple[bool, float, float, float]:
    """Check edge distinctness and overall separation ratio against diameter."""
    min_e, min_all, diam = _pair_metrics(pts, edges_c)
    ok = min_e > 1e-4 and (min_all / max(diam, 1e-12)) > 1e-5 and np.all(np.isfinite(pts))
    return ok, min_e, min_all, diam


def _scan_graph(task: tuple) -> dict:
    """Optimize 2D Re(A_G), 3D Re(A_G), and 3D |A_G| for one graph G."""
    name, n_verts, edges, n_starts_2d, n_starts_3d, maxiter, seed, early_stop = task
    edges_c = canonical_edges(edges)
    inv = _graph_invariants(n_verts, edges_c)
    G = nx.Graph(edges_c)
    G.add_nodes_from(range(n_verts))
    rng = np.random.default_rng(seed)

    p_col = np.array([[float(i), 0.0, 0.0] for i in range(n_verts)], dtype=np.float64)
    col_val = g_amplitude(n_verts, edges_c, p_col)
    scale = max(1.0, abs(col_val)) if np.isfinite(col_val.real) else 1.0

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
        if min_e < 1e-4 or (min_all / max(diam, 1e-12)) < 1e-5:
            return None
        val = g_amplitude(n_verts, edges_c, pts)
        if not (math.isfinite(val.real) and math.isfinite(val.imag)):
            return None
        return val

    def obj_2d_re(theta: np.ndarray) -> float:
        val = eval_safe(unpack_2d(theta))
        return 1e9 if val is None else float(val.real / scale)

    def obj_3d_re(theta: np.ndarray) -> float:
        val = eval_safe(unpack_3d(theta))
        return 1e9 if val is None else float(val.real / scale)

    def obj_3d_abs(theta: np.ndarray) -> float:
        val = eval_safe(unpack_3d(theta))
        return 1e9 if val is None else float(abs(val) / scale)

    best_2d_re = float("inf")
    best_2d_pts: list[list[float]] | None = None
    best_2d_sep: tuple[float, float, float] = (0.0, 0.0, 0.0)

    for x0 in _generate_starts(G, n_verts, 2, n_starts_2d, rng):
        res = minimize(obj_2d_re, x0, method="BFGS", options={"maxiter": maxiter})
        pts = unpack_2d(res.x)
        ok, min_e, min_all, diam = _is_well_separated(pts, edges_c)
        if not ok:
            continue
        val = g_amplitude(n_verts, edges_c, pts)
        if math.isfinite(val.real) and val.real < best_2d_re:
            best_2d_re = float(val.real)
            best_2d_pts = pts.tolist()
            best_2d_sep = (min_e, min_all, diam)
        if early_stop and best_2d_re < -1e-2:
            break

    best_3d_re = float("inf")
    best_3d_re_pts: list[list[float]] | None = None
    best_3d_abs = float("inf")
    best_3d_abs_pts: list[list[float]] | None = None
    best_3d_abs_sep: tuple[float, float, float] = (0.0, 0.0, 0.0)

    for x0 in _generate_starts(G, n_verts, 3, n_starts_3d, rng):
        r1 = minimize(obj_3d_re, x0, method="BFGS", options={"maxiter": maxiter})
        pts1 = unpack_3d(r1.x)
        ok1, _, _, _ = _is_well_separated(pts1, edges_c)
        if ok1:
            v1 = g_amplitude(n_verts, edges_c, pts1)
            if math.isfinite(v1.real) and v1.real < best_3d_re:
                best_3d_re = float(v1.real)
                best_3d_re_pts = pts1.tolist()

        r2 = minimize(obj_3d_abs, x0, method="BFGS", options={"maxiter": maxiter})
        pts2 = unpack_3d(r2.x)
        ok2, min_e2, min_all2, diam2 = _is_well_separated(pts2, edges_c)
        if ok2:
            v2 = g_amplitude(n_verts, edges_c, pts2)
            av2 = abs(v2)
            if math.isfinite(av2) and av2 < best_3d_abs:
                best_3d_abs = float(av2)
                best_3d_abs_pts = pts2.tolist()
                best_3d_abs_sep = (min_e2, min_all2, diam2)
        if early_stop and best_3d_abs < 0.5 and best_3d_re < -1e-2:
            break

    return {
        "name": name,
        "collinear_val": float(col_val.real),
        "scale": float(scale),
        **inv,
        "min_2d_re": best_2d_re,
        "min_3d_re": best_3d_re,
        "min_3d_abs": best_3d_abs,
        "min_norm_2d_re": float(best_2d_re / scale),
        "min_edge_dist_2d": best_2d_sep[0],
        "min_all_dist_2d": best_2d_sep[1],
        "diameter_2d": best_2d_sep[2],
        "min_all_dist_3d": best_3d_abs_sep[1],
        "diameter_3d": best_3d_abs_sep[2],
        "best_2d_pts": best_2d_pts,
        "best_3d_re_pts": best_3d_re_pts,
        "best_3d_abs_pts": best_3d_abs_pts,
        "violates": bool(min(best_2d_re, best_3d_re, best_3d_abs) < 0.999),
    }


def _verify_mp50_row(row: dict) -> dict:
    """Verify violating candidate endpoints with 50-digit mpmath."""
    n_verts = row["n"]
    edges_c = row["edges"]
    checks: dict[str, dict] = {}
    for label, key_pts, fval in (
        ("2d_re", "best_2d_pts", row["min_2d_re"]),
        ("3d_re", "best_3d_re_pts", row["min_3d_re"]),
        ("3d_abs", "best_3d_abs_pts", row["min_3d_abs"]),
    ):
        pts = row.get(key_pts)
        if pts is None or fval >= 0.999:
            continue
        arr = np.asarray(pts, dtype=np.float64)
        min_e, min_all, diam = _pair_metrics(arr, edges_c)
        mp_val = g_amplitude_mp(n_verts, edges_c, pts, dps=50)
        mp_re = float(mp_val.real)
        mp_im = float(mp_val.imag)
        mp_abs = float(abs(mp_val))
        cmp_target = mp_abs if label == "3d_abs" else mp_re
        rel_err = abs(fval - cmp_target) / max(1.0, abs(cmp_target))
        im_ok = True if label != "2d_re" else abs(mp_im) < 1e-40
        sep_ok = min_e > 1e-4 and (min_all / max(diam, 1e-12)) > 1e-5
        checks[label] = {
            "mp_re": mp.nstr(mp_val.real, 30),
            "mp_im": mp.nstr(mp_val.imag, 30),
            "mp_abs": mp.nstr(abs(mp_val), 30),
            "float_val": fval,
            "rel_err": rel_err,
            "min_edge_dist": min_e,
            "min_all_dist": min_all,
            "diameter": diam,
            "ok": bool(rel_err < 1e-6 and im_ok and sep_ok),
        }
    return checks


def _stage_c_graphs() -> list[tuple[str, int, list[tuple[int, int]]]]:
    """Construct n=8 taxonomy spanning bridges, 2-conn, 3-conn, 4-conn, vertex-transitive, and bipartite."""
    def k4_base() -> list[tuple[int, int]]:
        return list(nx.complete_graph(4).edges()) + [
            (u + 4, v + 4) for u, v in nx.complete_graph(4).edges()
        ]

    k4_m1 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]  # missing edge (2,3); degs: 3,3,2,2
    k4_m1_r = [(4, 5), (4, 6), (4, 7), (5, 6), (5, 7)]  # missing edge (6,7)

    graphs: list[tuple[str, int, list[tuple[int, int]]]] = [
        # --- Bridge graphs (kappa = 1) ---
        ("barbell_K4_8", 8, k4_base() + [(3, 4)]),
        ("K4m1_deg3_b_K4", 8, k4_m1 + [(1, 4)] + [(u + 4, v + 4) for u, v in nx.complete_graph(4).edges()]),
        ("K4m1_deg2_b_K4", 8, k4_m1 + [(3, 4)] + [(u + 4, v + 4) for u, v in nx.complete_graph(4).edges()]),
        ("K4m1_b_K4m1", 8, k4_m1 + [(1, 5)] + k4_m1_r),
        ("K5_b_K3", 8, list(nx.complete_graph(5).edges()) + [(4, 5), (5, 6), (5, 7), (6, 7)]),
        ("K4_b_K3_plus_leaf", 8, list(nx.complete_graph(4).edges()) + [(3, 4), (4, 5), (4, 6), (5, 6), (6, 7)]),
        # --- 2-connected & bridgeless (kappa = 2 or 1) ---
        ("K4_eq_K4_2conn", 8, k4_base() + [(3, 4), (2, 5)]),
        ("K4_2e_share", 8, k4_base() + [(3, 4), (3, 5)]),
        ("K4m1_eq_K4_2conn", 8, k4_m1 + [(4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7), (3, 4), (2, 5)]),
        ("K4m1_eq_K4m1_2conn", 8, k4_m1 + k4_m1_r + [(3, 4), (2, 5)]),
        ("C4_eq_C4_2conn", 8, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4), (3, 4), (2, 5)]),
        ("C8", 8, list(nx.cycle_graph(8).edges())),
        ("wheel_W8", 8, list(nx.wheel_graph(8).edges())),
        # --- 3-connected & 4-connected & vertex-transitive ---
        ("K4_3e_3conn", 8, k4_base() + [(3, 4), (2, 5), (1, 6)]),
        ("K4xK2_4reg_4conn", 8, k4_base() + [(0, 4), (1, 5), (2, 6), (3, 7)]),
        ("K4xK2_plus1", 8, k4_base() + [(0, 4), (1, 5), (2, 6), (3, 7), (0, 5)]),
        ("K4xK2_plus2", 8, k4_base() + [(0, 4), (1, 5), (2, 6), (3, 7), (0, 5), (1, 6)]),
        ("Wagner_M8", 8, [(i, (i + 1) % 8) for i in range(8)] + [(i, i + 4) for i in range(4)]),
        ("circulant_8_1_2", 8, list(nx.circulant_graph(8, [1, 2]).edges())),
        ("antiprism_4", 8, [(i, (i + 1) % 4) for i in range(4)] + [(4 + i, 4 + (i + 1) % 4) for i in range(4)] + [(i, 4 + i) for i in range(4)] + [(i, 4 + (i - 1) % 4) for i in range(4)]),
        # --- Bipartite n = 8 ---
        ("Q3_cube", 8, list(nx.convert_node_labels_to_integers(nx.cubical_graph()).edges())),
        ("K4_4_bip", 8, list(nx.complete_bipartite_graph(4, 4).edges())),
        ("K3_5_bip", 8, list(nx.complete_bipartite_graph(3, 5).edges())),
        ("K2_6_bip", 8, list(nx.complete_bipartite_graph(2, 6).edges())),
        ("double_star_3_3", 8, [(0, 1), (0, 2), (0, 3), (0, 4), (4, 5), (4, 6), (4, 7)]),
    ]
    return graphs


def _find_small_integer_witness(row: dict) -> dict | None:
    """Round a violating 2D float configuration to small integers verified at 50 digits."""
    if row["best_2d_pts"] is None or row["min_2d_re"] >= -1e-2:
        return None
    n_verts = row["n"]
    edges_c = row["edges"]
    pts_f = np.asarray(row["best_2d_pts"], dtype=np.float64)[:, :2]
    # Center and normalize so min pairwise distance is appreciable across candidate scales
    _, min_all, diam = _pair_metrics(np.column_stack([pts_f, np.zeros(n_verts)]), edges_c)
    scale_base = max(diam, 1.0)
    rng = np.random.default_rng(12345)

    best_int = None
    best_max_abs = float("inf")
    for mult in (30.0, 60.0, 120.0, 250.0, 600.0, 1500.0):
        arr = np.rint(pts_f * (mult / scale_base)).astype(int)
        # Shift so vertex 0 or centroid is clean
        arr = arr - np.rint(np.mean(arr, axis=0)).astype(int)
        # Ensure all points distinct
        pts3 = np.column_stack([arr.astype(float), np.zeros(n_verts)])
        min_e, min_all_i, _ = _pair_metrics(pts3, edges_c)
        if min_all_i < 0.5 or min_e < 0.5:
            continue
        val = g_amplitude(n_verts, edges_c, pts3)
        if math.isfinite(val.real) and val.real < -1e-2:
            # Try greedy coordinate shrink toward smaller integers while preserving Re < 0
            cur = arr.copy()
            for step in range(40):
                improved = False
                for v in range(n_verts):
                    for d in (0, 1):
                        if cur[v, d] == 0:
                            continue
                        cand = cur.copy()
                        cand[v, d] = int(round(cand[v, d] * 0.7))
                        pts_c = np.column_stack([cand.astype(float), np.zeros(n_verts)])
                        me, ma, _ = _pair_metrics(pts_c, edges_c)
                        if ma >= 0.5 and me >= 0.5:
                            vc = g_amplitude(n_verts, edges_c, pts_c)
                            if math.isfinite(vc.real) and vc.real < -1e-2:
                                cur = cand
                                improved = True
                if not improved:
                    break
            max_abs = int(np.max(np.abs(cur)))
            if max_abs < best_max_abs:
                best_max_abs = max_abs
                best_int = cur
            break

    if best_int is None:
        return None

    pts_list = [[float(r[0]), float(r[1]), 0.0] for r in best_int]
    mp_neg = g_amplitude_mp(n_verts, edges_c, pts_list, dps=50)
    # Check x-distinct collinearity along x-axis (for IVT homotopy if all x distinct)
    xs = [int(r[0]) for r in best_int]
    x_distinct = len(set(xs)) == n_verts
    pts_col = [[float(r[0]), 0.0, 0.0] for r in best_int]
    mp_col = g_amplitude_mp(n_verts, edges_c, pts_col, dps=50) if x_distinct else None
    pyth = None
    try:
        pyth = exact_gaussian_amplitude(n_verts, edges_c, [(int(r[0]), int(r[1])) for r in best_int])
    except ValueError:
        pyth = None

    return {
        "name": row["name"],
        "n": n_verts,
        "m": row["m"],
        "edges": edges_c,
        "pts_xy_int": [[int(r[0]), int(r[1])] for r in best_int],
        "max_coord_abs": int(best_max_abs),
        "x_distinct": x_distinct,
        "mp50_neg_re": mp.nstr(mp_neg.real, 35),
        "mp50_neg_im": mp.nstr(mp_neg.imag, 15),
        "mp50_col_re": mp.nstr(mp_col.real, 25) if mp_col is not None else None,
        "exact_pythagorean": pyth,
    }


def run_scan(workers: int = 12) -> dict:
    """Execute Stages A, B, C, and D across n=6, 7, 8 and verify with 50-digit mpmath."""
    t_all = time.monotonic()
    atlas = nx.graph_atlas_g()

    # --- Stage A: All 112 connected n=6 graphs ---
    t0 = time.monotonic()
    conn6 = [g for g in atlas if g.number_of_nodes() == 6 and nx.is_connected(g)]
    tasks6 = [
        (f"n6_idx{g.graph.get('name', i)}_{i}", 6, list(g.edges()), 10, 6, 100, 1000 + i, True)
        for i, g in enumerate(conn6)
    ]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        res6 = list(pool.map(_scan_graph, tasks6))
    dt6 = round(time.monotonic() - t0, 2)
    viol6 = [r for r in res6 if r["violates"]]
    min6_2d = min(r["min_2d_re"] for r in res6)
    min6_3d_re = min(r["min_3d_re"] for r in res6)
    min6_3d_abs = min(r["min_3d_abs"] for r in res6)
    print(
        f"[Stage A: n=6] {len(res6)} connected graphs in {dt6}s | "
        f"min_2d_re={min6_2d:.6f}, min_3d_re={min6_3d_re:.6f}, min_3d_abs={min6_3d_abs:.6f} | "
        f"violations={len(viol6)}"
    )

    # --- Stage B Pass 1: All 853 connected n=7 graphs ---
    t0 = time.monotonic()
    conn7 = [g for g in atlas if g.number_of_nodes() == 7 and nx.is_connected(g)]
    tasks7_p1 = [
        (f"n7_{i}_m{g.number_of_edges()}", 7, list(g.edges()), 8, 4, 80, 10000 + i, True)
        for i, g in enumerate(conn7)
    ]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        res7_p1 = list(pool.map(_scan_graph, tasks7_p1))
    dt7_p1 = round(time.monotonic() - t0, 2)
    viol7_p1 = [r for r in res7_p1 if r["violates"]]
    print(
        f"[Stage B Pass 1: n=7] {len(res7_p1)} connected graphs in {dt7_p1}s | "
        f"min_2d_re={min(r['min_2d_re'] for r in res7_p1):.6f}, "
        f"min_3d_re={min(r['min_3d_re'] for r in res7_p1):.6f}, "
        f"min_3d_abs={min(r['min_3d_abs'] for r in res7_p1):.6f} | "
        f"min_norm_2d_re={min(r['min_norm_2d_re'] for r in res7_p1):.6f} | "
        f"violations={len(viol7_p1)}"
    )

    # --- Stage B Pass 2: Top 40 lowest + targeted n=7 suspects ---
    t0 = time.monotonic()
    by_abs = sorted(range(len(res7_p1)), key=lambda idx: min(res7_p1[idx]["min_2d_re"], res7_p1[idx]["min_3d_re"], res7_p1[idx]["min_3d_abs"]))
    by_norm = sorted(range(len(res7_p1)), key=lambda idx: res7_p1[idx]["min_norm_2d_re"])
    deep_idxs = []
    seen_idx = set()
    for idx in by_abs[:25] + by_norm[:25]:
        if idx not in seen_idx:
            seen_idx.add(idx)
            deep_idxs.append(idx)
    tasks7_p2 = [
        (f"deep_{res7_p1[idx]['name']}", 7, res7_p1[idx]["edges"], 24, 14, 180, 30000 + idx, False)
        for idx in deep_idxs
    ]
    targeted_7 = [
        ("K4_v_K4_n7", 7, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]),
        ("K4_b_K3_n7", 7, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4), (4, 5), (4, 6), (5, 6)]),
        ("K5_b_K2_n7", 7, list(nx.complete_graph(5).edges()) + [(4, 5), (5, 6)]),
        ("K5_v_K3_n7", 7, list(nx.complete_graph(5).edges()) + [(4, 5), (4, 6), (5, 6)]),
        ("K4_2e_K3_2conn_n7", 7, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4), (2, 5), (4, 5), (4, 6), (5, 6)]),
        ("K7_minus_e_n7", 7, list(nx.complete_graph(7).edges())[1:]),
        ("K7_minus_M3_n7", 7, [e for e in nx.complete_graph(7).edges() if e not in {(0, 4), (1, 5), (2, 6)}]),
    ]
    for j, (nm, nv, ed) in enumerate(targeted_7):
        tasks7_p2.append((nm, nv, ed, 24, 14, 180, 40000 + j, False))

    with ProcessPoolExecutor(max_workers=workers) as pool:
        res7_p2 = list(pool.map(_scan_graph, tasks7_p2))
    dt7_p2 = round(time.monotonic() - t0, 2)
    viol7_p2 = [r for r in res7_p2 if r["violates"]]
    print(
        f"[Stage B Pass 2: n=7 deep] {len(res7_p2)} graphs in {dt7_p2}s | "
        f"min_2d_re={min(r['min_2d_re'] for r in res7_p2):.6f}, "
        f"min_3d_re={min(r['min_3d_re'] for r in res7_p2):.6f}, "
        f"min_3d_abs={min(r['min_3d_abs'] for r in res7_p2):.6f} | "
        f"violations={len(viol7_p2)}"
    )

    # --- Stage C: n=8 connectivity/symmetry/bipartite taxonomy ---
    t0 = time.monotonic()
    stage_c_defs = _stage_c_graphs()
    tasks8 = [
        (nm, nv, ed, 16, 8, 140, 50000 + i, False)
        for i, (nm, nv, ed) in enumerate(stage_c_defs)
    ]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        res8 = list(pool.map(_scan_graph, tasks8))
    dt8 = round(time.monotonic() - t0, 2)
    viol8 = [r for r in res8 if r["violates"]]
    print(f"[Stage C: n=8 taxonomy] {len(res8)} graphs in {dt8}s | violations={len(viol8)}")
    for r in res8:
        flag = "VIOLATES" if r["violates"] else "ok"
        print(
            f"  {r['name']:22s} m={r['m']:2d} kappa={r['node_connectivity']} "
            f"bridge={r['num_bridges']} bip={str(r['is_bipartite'])[0]} "
            f"planar={str(r['is_planar'])[0]} reg={str(r['is_regular'])[0]} | "
            f"2d_re={r['min_2d_re']:13.4f} 3d_abs={r['min_3d_abs']:11.4f} [{flag}]"
        )

    # --- Independent 50-digit mpmath verification on ALL violations ---
    t0 = time.monotonic()
    all_viol_rows = viol6 + viol7_p1 + viol7_p2 + viol8
    mp_verifications = []
    for row in all_viol_rows:
        checks = _verify_mp50_row(row)
        all_ok = bool(checks) and all(c["ok"] for c in checks.values())
        row["verified_mp50"] = all_ok
        row["mp50_checks"] = checks
        mp_verifications.append({"name": row["name"], "n": row["n"], "verified_mp50": all_ok, "checks": checks})

    # Also verify non-violating extreme low n=7 rows and Stage D integer witnesses
    witness_targets = viol7_p1 + viol7_p2 + [
        r for r in res8 if r["name"] in {"K4_eq_K4_2conn", "K4xK2_4reg_4conn", "Wagner_M8", "K4m1_eq_K4m1_2conn"}
    ]
    integer_witnesses = []
    for row in witness_targets:
        w = _find_small_integer_witness(row)
        if w is not None:
            integer_witnesses.append(w)

    # Trim point arrays from non-violating n=6/n=7 atlas rows to keep JSON compact
    def _compact(row: dict) -> dict:
        if row["violates"] or row["n"] == 8:
            return row
        out = dict(row)
        out.pop("best_2d_pts", None)
        out.pop("best_3d_re_pts", None)
        out.pop("best_3d_abs_pts", None)
        return out

    # Record top 15 lowest n=6 and n=7 summary rows cleanly
    top6 = sorted([_compact(r) for r in res6], key=lambda x: min(x["min_2d_re"], x["min_3d_re"], x["min_3d_abs"]))[:10]
    top7_p1 = sorted([_compact(r) for r in res7_p1], key=lambda x: min(x["min_2d_re"], x["min_3d_re"], x["min_3d_abs"]))[:15]
    top7_p1_norm = sorted([_compact(r) for r in res7_p1], key=lambda x: x["min_norm_2d_re"])[:10]

    total_dt = round(time.monotonic() - t_all, 2)
    return {
        "total_duration_sec": total_dt,
        "stage_a_n6": {
            "count": len(res6),
            "duration_sec": dt6,
            "min_2d_re": min6_2d,
            "min_3d_re": min6_3d_re,
            "min_3d_abs": min6_3d_abs,
            "violations": [_compact(r) for r in viol6],
            "top_10_lowest": top6,
        },
        "stage_b_n7_pass1": {
            "count": len(res7_p1),
            "duration_sec": dt7_p1,
            "min_2d_re": min(r["min_2d_re"] for r in res7_p1),
            "min_3d_re": min(r["min_3d_re"] for r in res7_p1),
            "min_3d_abs": min(r["min_3d_abs"] for r in res7_p1),
            "min_norm_2d_re": min(r["min_norm_2d_re"] for r in res7_p1),
            "violations": [_compact(r) for r in viol7_p1],
            "top_15_lowest": top7_p1,
            "top_10_lowest_normalized": top7_p1_norm,
        },
        "stage_b_n7_pass2_deep": {
            "count": len(res7_p2),
            "duration_sec": dt7_p2,
            "min_2d_re": min(r["min_2d_re"] for r in res7_p2),
            "min_3d_re": min(r["min_3d_re"] for r in res7_p2),
            "min_3d_abs": min(r["min_3d_abs"] for r in res7_p2),
            "min_norm_2d_re": min(r["min_norm_2d_re"] for r in res7_p2),
            "violations": [_compact(r) for r in viol7_p2],
            "rows": [_compact(r) for r in sorted(res7_p2, key=lambda x: min(x["min_2d_re"], x["min_3d_re"], x["min_3d_abs"]))],
        },
        "stage_c_n8_taxonomy": {
            "count": len(res8),
            "duration_sec": dt8,
            "violations_count": len(viol8),
            "rows": res8,
        },
        "mp50_verifications": mp_verifications,
        "integer_witnesses": integer_witnesses,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Exhaustive n=6,7 minimality and n=8 connectivity scan.")
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "data" / "minimality_and_connectivity_scan.json",
    )
    args = parser.parse_args()
    out = run_scan(workers=args.workers)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"Wrote {args.output} in {out['total_duration_sec']}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
