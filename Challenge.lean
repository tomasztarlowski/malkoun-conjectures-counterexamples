module

public import Mathlib

/-!
# Challenge: Counterexamples to All Four Malkoun Conjectures (A–D) & Unconditional Path Positivity

This lightweight Challenge module declares Malkoun's `G`-amplitude definitions
(`arXiv:2508.13472v3`), graph connectivity predicates, explicit witness graphs
(`k4e2k3Graph`, `wagnerGraph`, `cherryTree10`, `pathGraphN`), Conjectures C and D, and
12 headline theorems refuting all four main conjectures (A, B, C, D) and Section 6 while
proving Path Conjecture B and Planar Path Conjecture C unconditionally for all `n`.

## Scope of Compared Declarations, Proof Constructions, and Numerical Observations

- **General existential/negation theorems (6 declarations):**
  `disproof_malkoun_conjecture_A`, `disproof_malkoun_conjecture_B`,
  `disproof_malkoun_section_6`, `disproof_malkoun_conjecture_D`,
  `disproof_malkoun_rank2_conjecture_D`, and `disproof_malkoun_conjecture_C` state pure
  negations or existential refutations without fixing a witness inside their signatures;
  the explicit constructions (`barbellK4Graph` $B_8$, rank-3 $4\times 6$ witness on $C_6$,
  rank-2 $2\times 12$ Gaussian-integer witness on $C_{12}$, and $T_{10}$) live inside
  `Solution.lean` and `Matematyka/`.
- **Witness-pinned formal theorems (4 declarations):**
  `disproof_malkoun_n7_biconnected_conjecture_A`,
  `disproof_malkoun_wagner_triangleFree_conjecture_A`,
  `disproof_malkoun_tree_conjecture_A`, and `disproof_malkoun_path_conjecture_C_neg_re`
  explicitly bind `k4e2k3Graph` ($H_7$ on `Fin 7`), `wagnerGraph` ($M_8$ on `Fin 8`),
  `cherryTree10` ($T_{10}$ on `Fin 10`), and `pathGraphN 15` ($LG_{15}$ on `Fin 15`),
  together with coplanarity (`∀ u, x.1 u 2 = 0`, points in $\mathbb{R}^2 \times \{0\}$)
  where stated. Topological graph planarity of $H_7$ and vertex-transitivity of $M_8$ are
  elementary background graph-theoretic remarks outside this Lean formalization.
- **Unconditional path positivity (2 declarations):**
  `malkounAmplitude_pathGraphN_norm_ge_one` and
  `malkounAmplitude_pathGraphN_planar_re_ge_one` hold for every `n : ℕ`.
- **Empirical / numerical observations (not proved in Lean):**
  Absence of connected counterexamples on $n \le 6$ vertices and tree counterexamples on
  $4 \le n \le 9$ vertices (making $H_7$ and $T_{10}$ the smallest examples found in our scan),
  as well as 50-digit `mpmath` evaluations ($K_4 \square K_2$, $A_4$, $C_{18}$–$C_{28}$,
  $LG_{16}$–$LG_{17}$, spiders), are numerical search observations rather than formal proofs.

Proofs are supplied in `Solution.lean` and audited using strictly `{propext, Quot.sound, Classical.choice}`.
-/

@[expose] public section

namespace Challenge

open Complex Real
open scoped Classical ComplexOrder

/-- Configuration space $C_G(\mathbb{R}^3)$: adjacent vertices cannot collide. -/
def ConfigSpace {n : ℕ} (G : SimpleGraph (Fin n)) : Type :=
  { x : Fin n → Fin 3 → ℝ // ∀ u v, G.Adj u v → x u ≠ x v }

/-- Euclidean norm of a vector in $\mathbb{R}^3$. -/
noncomputable def euclidNorm (v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)

/-- Unit direction vector $v_{ij} = (\mathbf{x}_j - \mathbf{x}_i) / \|\mathbf{x}_j - \mathbf{x}_i\| \in S^2$. -/
noncomputable def unitDir (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => (b k - a k) / euclidNorm (fun j => b j - a j)

/-- Hermitian $2 \times 2$ matrix $v \cdot \vec{\sigma}$. -/
def pauliDot (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 2 : ℂ), (v 0 : ℂ) - Complex.I * (v 1 : ℂ);
     (v 0 : ℂ) + Complex.I * (v 1 : ℂ), -(v 2 : ℂ)]

/-- Skew-symmetric bilinear form $\omega$ on $\mathbb{C}^2$ (Malkoun Eq. (7)). -/
def omega (ψ φ : Fin 2 → ℂ) : ℂ :=
  ψ 0 * φ 1 - ψ 1 * φ 0

def unnormPos (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then ((1 + v 2 : ℝ) : ℂ) else (v 0 : ℂ) + Complex.I * (v 1 : ℂ)

def unnormNeg (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then (v 0 : ℂ) - Complex.I * (v 1 : ℂ) else ((1 - v 2 : ℝ) : ℂ)

/-- Canonical normalized $+1$-eigenvector of `pauliDot v` for unit `v ∈ S^2`. -/
noncomputable def canonicalSpinor (v : Fin 3 → ℝ) : Fin 2 → ℂ :=
  if 0 ≤ v 2 then
    ((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v
  else
    ((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v

/-- Canonical edge orientation $\Delta_\Gamma = \{(u, v) \in E : u < v\}$. -/
abbrev OriEdge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  { e : Fin n × Fin n // G.Adj e.1 e.2 ∧ e.1 < e.2 }

/-- Source-preserving permutation group $P_G = \prod_{u} \operatorname{Sym}(N_G(u))$. -/
abbrev SourcePerm {n : ℕ} (G : SimpleGraph (Fin n)) :=
  ∀ u : Fin n, Equiv.Perm { w : Fin n // G.Adj u w }

/-- Numerator of Malkoun's Eq. (13) $G$-amplitude. -/
noncomputable def malkounNum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  ∑ σ : SourcePerm G, ∏ e : OriEdge G,
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)

/-- Denominator of Malkoun's Eq. (13) $G$-amplitude. -/
def malkounDen {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  ∏ e : OriEdge G, omega (ψ e.1.1 e.1.2) (ψ e.1.2 e.1.1)

/-- Malkoun's $G$-amplitude given any family of spinors $\psi_{ij}$. -/
noncomputable def malkounAmplitudeOfSpinors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  malkounNum G ψ / malkounDen G ψ

/-- Canonical Malkoun $G$-amplitude $\mathcal{A}_G(\mathbf{x})$ on $C_G(\mathbb{R}^3)$. -/
noncomputable def malkounAmplitude {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : ConfigSpace G) : ℂ :=
  malkounAmplitudeOfSpinors G (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v)))

/-- Graph is 2-vertex-connected (`|V| ≥ 3`, connected, and every 1-vertex deletion stays connected). -/
def IsTwoVertexConnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  3 ≤ n ∧ G.Connected ∧ ∀ c : Fin n, (G.induce {x : Fin n | x ≠ c}).Connected

/-- Graph is 3-vertex-connected (`|V| ≥ 4`, connected, and every 2-vertex deletion stays connected). -/
def IsThreeVertexConnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  4 ≤ n ∧ G.Connected ∧ ∀ c₁ c₂ : Fin n, (G.induce {x : Fin n | x ≠ c₁ ∧ x ≠ c₂}).Connected

/-- Partition-preserving subgroup of `Equiv.Perm E`. -/
def partitionSubgroup {E V : Type*} (κ : E → V) : Subgroup (Equiv.Perm E) where
  carrier := { σ | ∀ e, κ (σ e) = κ e }
  one_mem' _ := rfl
  mul_mem' h1 h2 e := (h1 _).trans (h2 e)
  inv_mem' {a} h e :=
    ((h (a⁻¹ e)).symm).trans (congrArg (fun g : Equiv.Perm E => κ (g e)) (mul_inv_cancel a))

/-- Matrix-analytic **Conjecture D** of Malkoun (`arXiv:2508.13472v3`, Section 4). -/
def MalkounConjectureDProp : Prop :=
  ∀ (E V₁ V₂ : Type) [Fintype E] [DecidableEq E] (κ₁ : E → V₁) (κ₂ : E → V₂)
    (H : Matrix E E ℂ),
    H.PosSemidef →
    (∑ σ₁ : partitionSubgroup κ₁, ∑ σ₂ : partitionSubgroup κ₂,
      ∏ e : E, H (σ₁.1 e) (σ₂.1 e)).re ≥
      (Fintype.card ↥(partitionSubgroup κ₁ ⊓ partitionSubgroup κ₂) : ℝ) *
        ∏ e : E, (H e e).re

/-- **Rank-2 Spinor Conjecture D:** Conjecture D restricted to rank-2 Gram matrices $H = B^H B$. -/
def MalkounRank2ConjectureDProp : Prop :=
  ∀ (E V₁ V₂ : Type) [Fintype E] [DecidableEq E] (κ₁ : E → V₁) (κ₂ : E → V₂)
    (B : Matrix (Fin 2) E ℂ),
    let H := B.conjTranspose * B
    (∑ σ₁ : partitionSubgroup κ₁, ∑ σ₂ : partitionSubgroup κ₂,
      ∏ e : E, H (σ₁.1 e) (σ₂.1 e)).re ≥
      (Fintype.card ↥(partitionSubgroup κ₁ ⊓ partitionSubgroup κ₂) : ℝ) *
        ∏ e : E, (H e e).re

/-- **Malkoun's Conjecture C (`arXiv:2508.13472v3`, Section 4):** for every finite tree `T`,
$\operatorname{Re}(\mathcal{A}_T(\mathbf{x})) \ge 1$. -/
def MalkounConjectureCProp : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (_ : DecidableRel T.Adj),
    T.IsTree → ∀ x : ConfigSpace T, 1 ≤ (malkounAmplitude T x).re

/-- Linear path graph $LG_n$ on `Fin n`. -/
def pathGraphN (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => h.elim (Nat.succ_ne_self u.val) (Nat.succ_ne_self u.val)⟩

instance instDecidableRelPathN (n : ℕ) : DecidableRel (pathGraphN n).Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)))

/-- Symmetric irreflexive simple graph on `Fin n` induced by a Boolean generator `b`. -/
def mkGraphOfBool {n : ℕ} (b : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (b u v = true ∨ b v u = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableRelMkGraphOfBool {n : ℕ} (b : Fin n → Fin n → Bool) :
    DecidableRel (mkGraphOfBool b).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (b u v = true ∨ b v u = true)))

/-- Directed edge generator for the 7-vertex, 11-edge graph $H_7 = K_4 \cup_{2e} K_3$. -/
def k4e2k3GenBool (u v : Fin 7) : Bool :=
  (u.val ≤ 3 && v.val ≤ 3) ||
  (4 ≤ u.val && 4 ≤ v.val) ||
  (u.val == 2 && v.val == 5) ||
  (u.val == 3 && v.val == 4)

/-- Explicit 7-vertex, 11-edge graph $H_7 = K_4 \cup_{2e} K_3$ on `Fin 7`. -/
def k4e2k3Graph : SimpleGraph (Fin 7) := mkGraphOfBool k4e2k3GenBool

instance instDecidableRelK4e2k3 : DecidableRel k4e2k3Graph.Adj :=
  instDecidableRelMkGraphOfBool k4e2k3GenBool

/-- Directed edge generator for the 8-vertex, 12-edge cubic Möbius ladder $M_8$ (Wagner graph). -/
def wagnerGenBool (u v : Fin 8) : Bool :=
  (u.val == 0 && v.val == 1) || (u.val == 1 && v.val == 2) ||
  (u.val == 2 && v.val == 3) || (u.val == 3 && v.val == 4) ||
  (u.val == 4 && v.val == 5) || (u.val == 5 && v.val == 6) ||
  (u.val == 6 && v.val == 7) || (u.val == 7 && v.val == 0) ||
  (u.val == 0 && v.val == 4) || (u.val == 1 && v.val == 5) ||
  (u.val == 2 && v.val == 6) || (u.val == 3 && v.val == 7)

/-- Explicit 8-vertex, 12-edge Wagner graph $M_8$ on `Fin 8`. -/
def wagnerGraph : SimpleGraph (Fin 8) := mkGraphOfBool wagnerGenBool

instance instDecidableRelWagner : DecidableRel wagnerGraph.Adj :=
  instDecidableRelMkGraphOfBool wagnerGenBool

/-- Directed edge generator for the 10-vertex, 9-edge cubic cherry tree $T_{10}$. -/
def cherry10GenBool (u v : Fin 10) : Bool :=
  (u.val == 0 && (v.val == 1 || v.val == 4 || v.val == 7)) ||
  (u.val == 1 && (v.val == 2 || v.val == 3)) ||
  (u.val == 4 && (v.val == 5 || v.val == 6)) ||
  (u.val == 7 && (v.val == 8 || v.val == 9))

/-- Explicit 10-vertex, 9-edge cubic cherry tree $T_{10}$ on `Fin 10`. -/
def cherryTree10 : SimpleGraph (Fin 10) := mkGraphOfBool cherry10GenBool

instance instDecidableRelCherry10 : DecidableRel cherryTree10.Adj :=
  instDecidableRelMkGraphOfBool cherry10GenBool

/-- Disproof of Malkoun's Conjecture A (`∃ G` connected, `x ∈ C_G(ℝ³)`, `A_G(x) = 0`),
proved in `Solution` via the barbell graph `B_8`. -/
theorem disproof_malkoun_conjecture_A :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G, malkounAmplitude G x = 0 := by
  sorry

/-- Disproof of Malkoun's Conjecture B (`∃ G` connected, `x ∈ C_G(ℝ³)`, `‖A_G(x)‖ < 1`),
proved in `Solution` via the barbell graph `B_8`. -/
theorem disproof_malkoun_conjecture_B :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G, ‖malkounAmplitude G x‖ < 1 := by
  sorry

/-- Disproof of Malkoun's Section 6 connected-graph question (`Re(A_G) < 0`, `Im(A_G) = 0`),
proved in `Solution` via the barbell graph `B_8`. -/
theorem disproof_malkoun_section_6 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G,
        (malkounAmplitude G x).re < 0 ∧ (malkounAmplitude G x).im = 0 := by
  sorry

/-- Disproof of Conjecture A on the explicit 7-vertex 2-vertex-connected graph `k4e2k3Graph`
($H_7 = K_4 \cup_{2e} K_3$) via a planar point configuration (`∀ u, x.1 u 2 = 0`).
(Smallest counterexample found numerically; absence of $n \le 6$ violations is a numerical
search observation rather than a formal proof.) -/
theorem disproof_malkoun_n7_biconnected_conjecture_A :
    k4e2k3Graph.Connected ∧ IsTwoVertexConnected k4e2k3Graph ∧
      ∃ x : ConfigSpace k4e2k3Graph,
        (∀ u, x.1 u 2 = 0) ∧ malkounAmplitude k4e2k3Graph x = 0 := by
  sorry

/-- Disproof of Conjecture A on the explicit 8-vertex triangle-free 3-regular 3-vertex-connected
Wagner graph `wagnerGraph` ($M_8$) via a planar point configuration (`∀ u, x.1 u 2 = 0`). -/
theorem disproof_malkoun_wagner_triangleFree_conjecture_A :
    wagnerGraph.Connected ∧ IsThreeVertexConnected wagnerGraph ∧
      wagnerGraph.IsRegularOfDegree 3 ∧ wagnerGraph.CliqueFree 3 ∧
      ∃ x : ConfigSpace wagnerGraph,
        (∀ u, x.1 u 2 = 0) ∧ malkounAmplitude wagnerGraph x = 0 := by
  sorry

/-- Disproof of General Conjecture D, proved in `Solution` via a rank-3 matrix on `C_6`. -/
theorem disproof_malkoun_conjecture_D : ¬ MalkounConjectureDProp := by
  sorry

/-- Disproof of Rank-2 Spinor Conjecture D, proved in `Solution` via a `2 × 12` matrix on `C_12`. -/
theorem disproof_malkoun_rank2_conjecture_D : ¬ MalkounRank2ConjectureDProp := by
  sorry

/-- Disproof of Conjecture C on finite trees, proved in `Solution` via `cherryTree10` ($T_{10}$). -/
theorem disproof_malkoun_conjecture_C : ¬ MalkounConjectureCProp := by
  sorry

/-- Disproof of Conjecture A restricted to planar point configurations (`∀ u, x.1 u 2 = 0`) on
finite trees, proved on the explicit 10-vertex cubic cherry tree `cherryTree10` ($T_{10}$). -/
theorem disproof_malkoun_tree_conjecture_A :
    cherryTree10.IsTree ∧ ∃ x : ConfigSpace cherryTree10,
      Function.Injective x.1 ∧ (∀ u, x.1 u 2 = 0) ∧ malkounAmplitude cherryTree10 x = 0 := by
  sorry

/-- Disproof of Conjecture C restricted to linear path graphs: on the explicit 15-vertex path
`pathGraphN 15` ($LG_{15}$), there exists `x ∈ C_{LG_15}(ℝ³)` with exact negative rational real
part `-40605770611892600000 / 58001564658819600000 < 0`. -/
theorem disproof_malkoun_path_conjecture_C_neg_re :
    ∃ x : ConfigSpace (pathGraphN 15),
      (malkounAmplitude (pathGraphN 15) x).re =
        (-40605770611892600000 : ℝ) / 58001564658819600000 ∧
      (malkounAmplitude (pathGraphN 15) x).re < 0 := by
  sorry

/-- Unconditional Path Conjecture B for all $n \in \mathbb{N}$: $|\mathcal{A}_{LG_n}(\mathbf{x})| \ge 1$. -/
theorem malkounAmplitude_pathGraphN_norm_ge_one (n : ℕ) (x : ConfigSpace (pathGraphN n)) :
    1 ≤ ‖malkounAmplitude (pathGraphN n) x‖ := by
  sorry

/-- Unconditional Planar Path Conjecture C for all $n \in \mathbb{N}$: $\operatorname{Re}(\mathcal{A}_{LG_n}(\mathbf{x})) \ge 1$. -/
theorem malkounAmplitude_pathGraphN_planar_re_ge_one (n : ℕ) (x : ConfigSpace (pathGraphN n))
    (hplanar : ∀ u, x.1 u 2 = 0) :
    1 ≤ (malkounAmplitude (pathGraphN n) x).re := by
  sorry

end Challenge
