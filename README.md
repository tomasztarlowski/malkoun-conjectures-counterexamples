# Counterexamples to All Four Malkoun Conjectures (A–D), Planar Tree Zeros, and Unconditional Path Positivity

Machine-checked **Lean 4 (`v4.37.0-rc1` + Mathlib)** refutations of all four main conjectures (**A, B, C, D**) and the Section 6 real-positivity question from Joseph Malkoun's preprint [*Finite graphs and configurations of points*](https://arxiv.org/abs/2508.13472) (`arXiv:2508.13472v3`), together with unconditional positive theorems for arbitrary linear paths $LG_n$ and small trees.

- **Preprint manuscript:** [`paper/malkoun_counterexamples.tex`](paper/malkoun_counterexamples.tex) ([compiled PDF](paper/malkoun_counterexamples.pdf), 9 pages)
- **Axiom & Kernel Purity:** Zero `sorry`, zero `admit`, zero `native_decide` across all Lean modules; `#print axioms` and `comparator.json` verification depend strictly on `{propext, Classical.choice, Quot.sound}`.

---

## Summary of Kernel-Verified Results

| Result | Scope / Witness | Verdict | Key Lean 4 Declarations |
|---|---|---|---|
| **Conjectures A, B, Section 6** | Connected planar $K_4$-barbell $B_8$ ($n=8, m=13$) | **Disproved** | `disproof_malkoun_conjecture_A`, `disproof_malkoun_conjecture_B`, `disproof_malkoun_section_6` |
| **Vertex-minimal 2-connected** | Planar biconnected $H_7 = K_4 \cup_{2e} K_3$ ($n=7, m=11, \kappa=2$) | **Disproved** | `disproof_malkoun_n7_biconnected_conjecture_A` (`MalkounN7Counterexample.lean`) |
| **Triangle-free cubic 3-connected** | Wagner graph $M_8$ ($n=8, m=12, \kappa=3$, girth $4$) | **Disproved** | `disproof_malkoun_wagner_triangleFree_conjecture_A` (`MalkounWagnerCounterexample.lean`) |
| **General Bipartite Reduction** | Extension of Malkoun Thm. 4.1 to all bipartite graphs | **Proved** | `malkounAmplitude_bipartite_eq_conj_gram`, `conjectureD_implies_bipartite_re_ge_one` (`MalkounBipartite.lean`) |
| **General Conjecture D** | Explicit $4 \times 6$ rank-3 integer matrix on $C_6$ ($7 < 8$) | **Disproved** | `disproof_malkoun_conjecture_D` (`MalkounConjectureD.lean`) |
| **Rank-2 Spinor Conjecture D** | Explicit $2 \times 12$ Gaussian-integer matrix on $C_{12}$ ($\operatorname{Re} < 0$) | **Disproved** | `disproof_malkoun_rank2_conjecture_D` (`MalkounConjectureD.lean`) |
| **Conjecture C & Tree Conj. A, B, D** | Planar $120^\circ$ pinwheel zero $\mathcal{A}_{T_{10}} = 0$ ($n=10, m=9$) | **Disproved** | `disproof_malkoun_conjecture_C`, `disproof_malkoun_tree_conjecture_A`, `disproof_malkoun_tree_conjecture_D` (`MalkounConjectureC.lean`) |
| **Path Conjecture C ($\operatorname{Re} \ge 1$)** | Integer Hopf coordinates on $LG_{15}$ ($\operatorname{Re} \approx -0.700081 < 0$) | **Disproved** | `disproof_malkoun_path_conjecture_C_neg_re` (`MalkounConjectureC.lean`) |
| **Path Conjectures B & A (all $n$)** | Exact $\mathrm{SU}(2)$ hyperbolic Lyapunov invariant $|a_k|^2 - |\beta_k|^2 \ge 1$ | **Proved** | `malkounAmplitude_pathGraphN_norm_ge_one`, `malkounAmplitude_pathGraphN_ne_zero` (`MalkounPathPositivity.lean`) |
| **Planar Path Conjecture C (all $n$)** | Cayley-rotated real spinor gauge for $z_u \equiv 0$ | **Proved** | `malkounAmplitude_pathGraphN_planar_re_ge_one` (`MalkounPathPositivity.lean`) |
| **Small-Tree Positivity** | Unconditional $\operatorname{Re} \ge 1$ for $LG_3, LG_4, K_{1,3}, LG_5$ | **Proved** | `malkounAmplitude_path5_re_ge_one` (`MalkounConjectureD.lean`) |

In addition, 50-digit `mpmath` scans archived in `data/` exhibit:
- Higher-connectivity planar/non-planar $n=8$ witnesses (`K4xK2_4reg_4conn`, vertex-transitive square antiprism `antiprism_4`);
- Bipartite even-cycle violations ($|\mathcal{A}_{C_{18}}| \approx 0.9598 < 1$, $|\mathcal{A}_{C_{20}}| \approx 0.9026 < 1$, $\operatorname{Re}(\mathcal{A}_{C_{24}}) \approx -9962.05 < 0$);
- Exhaustive optimization over all **92** non-isomorphic trees on $4 \le n \le 9$ vertices (`2, 3, 6, 11, 23, 47`), all maintaining $\inf \RePart \ge 1$, while 4 trees fail at $n = 10$ alongside $LG_{16}, LG_{17}$ and 3-legged spiders `Spider(3,3,4)`, `Spider(3,4,4)`, `Spider(4,4,4)`.

---

## Repository Structure

```text
.
├── Matematyka.lean                          # Root module importing all 8 Malkoun libraries
├── Matematyka/
│   ├── Malkoun.lean                         # Core lemmas (Malkoun Lemma 5.1, 5.2, LG_3)
│   ├── MalkounCounterexample.lean           # B_8 barbell disproofs (Conj. A, B, Sec. 6)
│   ├── MalkounBipartite.lean                # General bipartite time-reversal Gram reduction
│   ├── MalkounN7Counterexample.lean         # Minimal biconnected planar n=7 (H_7) disproofs
│   ├── MalkounWagnerCounterexample.lean     # Triangle-free 3-connected cubic Wagner (M_8) disproofs
│   ├── MalkounConjectureD.lean              # General (m=6) & rank-2 (m=12) Conj. D disproofs + small trees
│   ├── MalkounConjectureC.lean              # T_10 planar tree zero + LG_{15} negative Re disproofs
│   └── MalkounPathPositivity.lean           # Unconditional Path Conj. B & Planar Path Conj. C (all n)
├── Challenge.lean                           # Self-contained Palomar/Comparator challenge statements (12 theorems)
├── Solution.lean                            # Verified proofs bridging Matematyka.Malkoun* -> Challenge
├── comparator.json                          # Comparator manifest & standard axiom allowlist
├── formalization.yaml                       # Mathlib Initiative metadata (schema v0.4)
├── paper/
│   ├── malkoun_counterexamples.tex          # LaTeX manuscript
│   └── malkoun_counterexamples.pdf          # Compiled 9-page PDF
├── scripts/                                 # Python/mpmath/SciPy search & certificate generation scripts
├── data/                                    # JSON witness coordinates and exact certificates
├── lean-toolchain                           # leanprover/lean4:v4.37.0-rc1
├── lakefile.toml
├── lake-manifest.json
└── LICENSE                                  # Apache-2.0
```

---

## Quick Reproduction

### 1. Build All Lean 4 Proofs (`Challenge`, `Solution`, and `Matematyka`)

```bash
lake exe cache get
lake build
rg -nw 'sorry|admit|native_decide' Matematyka/ Solution.lean
```

### 2. Reproduce 50-Digit `mpmath` Certificates & Searches

```bash
python3 -m pip install mpmath numpy scipy networkx
python3 scripts/scan_malkoun.py
python3 scripts/analyze_barbell_counterexample.py
python3 scripts/analyze_conjecture_d_and_cycles.py
python3 scripts/analyze_conjecture_c_trees.py
```

---

## Author & AI Disclosure

- **Author:** Tomasz Tarłowski (`tomasztarlowski`)
- **AI Assistance Disclosure:** Witness discovery, Python/mpmath optimization, Lean 4 proof engineering, and manuscript drafting were carried out in an interactive human–AI workflow using Gemini, Claude, and OpenAI Codex. All formal theorems are independently checked by the Lean 4 kernel (`{propext, Classical.choice, Quot.sound}` only).

## License

Licensed under the [Apache License 2.0](LICENSE).
