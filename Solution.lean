module

public import Mathlib
public import Matematyka.MalkounN7Counterexample
public import Matematyka.MalkounWagnerCounterexample
public import Matematyka.MalkounPathPositivity

/-!
# Solution: Counterexamples to All Four Malkoun Conjectures (A–D) & Unconditional Path Positivity

Supplies kernel-verified proofs for every theorem declared in `Challenge.lean` and audited in
`comparator.json`, bridging identically structured public definitions in `namespace Challenge` to
`Matematyka.Malkoun*`.
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

lemma pathGraphN_eq (n : ℕ) :
    pathGraphN n = Matematyka.MalkounPathPositivity.pathGraphN n :=
  rfl

lemma malkounAmplitude_eq_mat {n : ℕ} (G : SimpleGraph (Fin n))
    [inst1 : DecidableRel G.Adj] (inst2 : DecidableRel G.Adj)
    (x : ConfigSpace G) :
    @malkounAmplitude n G inst1 x =
      @Matematyka.MalkounCounterexample.malkounAmplitude n G inst2 x := by
  obtain rfl : inst1 = inst2 := Subsingleton.elim inst1 inst2
  rfl

lemma k4e2k3Graph_eq :
    k4e2k3Graph = Matematyka.MalkounN7Counterexample.k4e2k3Graph := by
  have h : ∀ u v : Fin 7,
      ((u != v) && (k4e2k3GenBool u v || k4e2k3GenBool v u)) =
        Matematyka.MalkounN7Counterexample.k4e2k3AdjBool u v := by
    decide
  ext u v
  change (u ≠ v ∧ (k4e2k3GenBool u v = true ∨ k4e2k3GenBool v u = true)) ↔
    Matematyka.MalkounN7Counterexample.k4e2k3AdjBool u v = true
  rw [← bne_iff_ne, ← Bool.or_eq_true, ← Bool.and_eq_true, h u v]

lemma wagnerGraph_eq :
    wagnerGraph = Matematyka.MalkounWagnerCounterexample.wagnerGraph := by
  have h : ∀ u v : Fin 8,
      ((u != v) && (wagnerGenBool u v || wagnerGenBool v u)) =
        Matematyka.MalkounWagnerCounterexample.wagnerAdjBool u v := by
    decide
  ext u v
  change (u ≠ v ∧ (wagnerGenBool u v = true ∨ wagnerGenBool v u = true)) ↔
    Matematyka.MalkounWagnerCounterexample.wagnerAdjBool u v = true
  rw [← bne_iff_ne, ← Bool.or_eq_true, ← Bool.and_eq_true, h u v]

lemma cherryTree10_eq :
    cherryTree10 = Matematyka.MalkounConjectureC.cherryTree10 := by
  have h : ∀ u v : Fin 10,
      ((u != v) && (cherry10GenBool u v || cherry10GenBool v u)) =
        @decide (Matematyka.MalkounConjectureC.cherryTree10.Adj u v)
          (Matematyka.MalkounConjectureC.instDecidableRelCherry10 u v) := by
    decide
  ext u v
  change (u ≠ v ∧ (cherry10GenBool u v = true ∨ cherry10GenBool v u = true)) ↔
    Matematyka.MalkounConjectureC.cherryTree10.Adj u v
  rw [← bne_iff_ne, ← Bool.or_eq_true, ← Bool.and_eq_true, h u v,
    @decide_eq_true_eq _ (Matematyka.MalkounConjectureC.instDecidableRelCherry10 u v)]

lemma pathGraphN15_eq :
    pathGraphN 15 = Matematyka.MalkounConjectureC.pathGraph15 := by
  ext u v
  rfl

lemma n7_bridge {G₁ G₂ : SimpleGraph (Fin 7)} (hG : G₁ = G₂)
    [inst1 : DecidableRel G₁.Adj] (inst2 : DecidableRel G₂.Adj)
    (hconn : G₂.Connected)
    (h2 : Matematyka.MalkounN7Counterexample.IsTwoVertexConnected G₂)
    (x₂ : Matematyka.MalkounCounterexample.ConfigSpace G₂)
    (hpl : ∀ u, x₂.1 u 2 = 0)
    (hz : @Matematyka.MalkounCounterexample.malkounAmplitude 7 G₂ inst2 x₂ = 0) :
    G₁.Connected ∧ IsTwoVertexConnected G₁ ∧
      ∃ x : ConfigSpace G₁, (∀ u, x.1 u 2 = 0) ∧ @malkounAmplitude 7 G₁ inst1 x = 0 := by
  subst hG
  obtain rfl : inst1 = inst2 := Subsingleton.elim inst1 inst2
  let x₁ : ConfigSpace G₁ := ⟨x₂.1, x₂.2⟩
  have hamp : @malkounAmplitude 7 G₁ inst1 x₁ =
      @Matematyka.MalkounCounterexample.malkounAmplitude 7 G₁ inst1 x₂ := rfl
  exact ⟨hconn, h2, x₁, hpl, hamp.trans hz⟩

lemma wagner_bridge {G₁ G₂ : SimpleGraph (Fin 8)} (hG : G₁ = G₂)
    [inst1 : DecidableRel G₁.Adj] (inst2 : DecidableRel G₂.Adj)
    (hconn : G₂.Connected)
    (h3 : Matematyka.MalkounWagnerCounterexample.IsThreeVertexConnected G₂)
    (hreg : @SimpleGraph.IsRegularOfDegree (Fin 8) G₂
      (fun v => @Subtype.fintype (Fin 8) (Membership.mem (G₂.neighborSet v))
        (fun a => @SimpleGraph.neighborSet.memDecidable (Fin 8) G₂ v inst2 a) (Fin.fintype 8)) 3)
    (hcf : G₂.CliqueFree 3)
    (x₂ : Matematyka.MalkounCounterexample.ConfigSpace G₂)
    (hpl : ∀ u, x₂.1 u 2 = 0)
    (hz : @Matematyka.MalkounCounterexample.malkounAmplitude 8 G₂ inst2 x₂ = 0) :
    G₁.Connected ∧ IsThreeVertexConnected G₁ ∧
      @SimpleGraph.IsRegularOfDegree (Fin 8) G₁
        (fun v => @Subtype.fintype (Fin 8) (Membership.mem (G₁.neighborSet v))
          (fun a => @SimpleGraph.neighborSet.memDecidable (Fin 8) G₁ v inst1 a) (Fin.fintype 8)) 3 ∧
      G₁.CliqueFree 3 ∧
      ∃ x : ConfigSpace G₁, (∀ u, x.1 u 2 = 0) ∧ @malkounAmplitude 8 G₁ inst1 x = 0 := by
  subst hG
  obtain rfl : inst1 = inst2 := Subsingleton.elim inst1 inst2
  let x₁ : ConfigSpace G₁ := ⟨x₂.1, x₂.2⟩
  have hamp : @malkounAmplitude 8 G₁ inst1 x₁ =
      @Matematyka.MalkounCounterexample.malkounAmplitude 8 G₁ inst1 x₂ := rfl
  exact ⟨hconn, h3, hreg, hcf, x₁, hpl, hamp.trans hz⟩

lemma cherry10_bridge {G₁ G₂ : SimpleGraph (Fin 10)} (hG : G₁ = G₂)
    [inst1 : DecidableRel G₁.Adj] (inst2 : DecidableRel G₂.Adj)
    (htree : G₂.IsTree)
    (x₂ : Matematyka.MalkounCounterexample.ConfigSpace G₂)
    (hinj : Function.Injective x₂.1)
    (hpl : ∀ u, x₂.1 u 2 = 0)
    (hz : @Matematyka.MalkounCounterexample.malkounAmplitude 10 G₂ inst2 x₂ = 0) :
    G₁.IsTree ∧ ∃ x : ConfigSpace G₁,
      Function.Injective x.1 ∧ (∀ u, x.1 u 2 = 0) ∧ @malkounAmplitude 10 G₁ inst1 x = 0 := by
  subst hG
  obtain rfl : inst1 = inst2 := Subsingleton.elim inst1 inst2
  let x₁ : ConfigSpace G₁ := ⟨x₂.1, x₂.2⟩
  have hamp : @malkounAmplitude 10 G₁ inst1 x₁ =
      @Matematyka.MalkounCounterexample.malkounAmplitude 10 G₁ inst1 x₂ := rfl
  exact ⟨htree, x₁, hinj, hpl, hamp.trans hz⟩

lemma lg15_bridge {G₁ G₂ : SimpleGraph (Fin 15)} (hG : G₁ = G₂)
    [inst1 : DecidableRel G₁.Adj] (inst2 : DecidableRel G₂.Adj)
    (x₂ : Matematyka.MalkounCounterexample.ConfigSpace G₂)
    (hre : (@Matematyka.MalkounCounterexample.malkounAmplitude 15 G₂ inst2 x₂).re =
      (-40605770611892600000 : ℝ) / 58001564658819600000) :
    ∃ x : ConfigSpace G₁,
      (@malkounAmplitude 15 G₁ inst1 x).re =
        (-40605770611892600000 : ℝ) / 58001564658819600000 ∧
      (@malkounAmplitude 15 G₁ inst1 x).re < 0 := by
  subst hG
  obtain rfl : inst1 = inst2 := Subsingleton.elim inst1 inst2
  let x₁ : ConfigSpace G₁ := ⟨x₂.1, x₂.2⟩
  have hamp : @malkounAmplitude 15 G₁ inst1 x₁ =
      @Matematyka.MalkounCounterexample.malkounAmplitude 15 G₁ inst1 x₂ := rfl
  refine ⟨x₁, ?_, ?_⟩
  · rw [hamp, hre]
  · rw [hamp, hre]; norm_num

/-- Disproof of Malkoun's Conjecture A (`∃ G` connected, `x ∈ C_G(ℝ³)`, `A_G(x) = 0`),
proved in `Solution` via the barbell graph `B_8`. -/
theorem disproof_malkoun_conjecture_A :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G, malkounAmplitude G x = 0 := by
  rcases Matematyka.MalkounCounterexample.disproof_malkoun_conjecture_A with
    ⟨n, G, inst, hconn, x, hx⟩
  exact ⟨n, G, inst, hconn, x, hx⟩

/-- Disproof of Malkoun's Conjecture B (`∃ G` connected, `x ∈ C_G(ℝ³)`, `‖A_G(x)‖ < 1`),
proved in `Solution` via the barbell graph `B_8`. -/
theorem disproof_malkoun_conjecture_B :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G, ‖malkounAmplitude G x‖ < 1 := by
  rcases Matematyka.MalkounCounterexample.disproof_malkoun_conjecture_B with
    ⟨n, G, inst, hconn, x, hx⟩
  exact ⟨n, G, inst, hconn, x, hx⟩

/-- Disproof of Malkoun's Section 6 connected-graph question (`Re(A_G) < 0`, `Im(A_G) = 0`),
proved in `Solution` via the barbell graph `B_8`. -/
theorem disproof_malkoun_section_6 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G,
        (malkounAmplitude G x).re < 0 ∧ (malkounAmplitude G x).im = 0 := by
  rcases Matematyka.MalkounCounterexample.disproof_malkoun_section_6 with
    ⟨n, G, inst, hconn, x, hre, him⟩
  exact ⟨n, G, inst, hconn, x, hre, him⟩

/-- Disproof of Conjecture A on the explicit 7-vertex 2-vertex-connected graph `k4e2k3Graph`
($H_7 = K_4 \cup_{2e} K_3$) via a planar point configuration (`∀ u, x.1 u 2 = 0`).
(Smallest counterexample found numerically; absence of $n \le 6$ violations is a numerical
search observation rather than a formal proof.) -/
theorem disproof_malkoun_n7_biconnected_conjecture_A :
    k4e2k3Graph.Connected ∧ IsTwoVertexConnected k4e2k3Graph ∧
      ∃ x : ConfigSpace k4e2k3Graph,
        (∀ u, x.1 u 2 = 0) ∧ malkounAmplitude k4e2k3Graph x = 0 := by
  rcases Matematyka.MalkounN7Counterexample.exists_n7Path_zero with ⟨t₀, _, ht₀⟩
  exact n7_bridge k4e2k3Graph_eq Matematyka.MalkounN7Counterexample.instDecidableRelK4e2k3
    Matematyka.MalkounN7Counterexample.k4e2k3Graph_connected
    Matematyka.MalkounN7Counterexample.k4e2k3Graph_twoVertexConnected
    (Matematyka.MalkounN7Counterexample.n7Path t₀)
    (Matematyka.MalkounN7Counterexample.n7Path_planar t₀)
    ht₀

/-- Disproof of Conjecture A on the explicit 8-vertex triangle-free 3-regular 3-vertex-connected
Wagner graph `wagnerGraph` ($M_8$) via a planar point configuration (`∀ u, x.1 u 2 = 0`). -/
theorem disproof_malkoun_wagner_triangleFree_conjecture_A :
    wagnerGraph.Connected ∧ IsThreeVertexConnected wagnerGraph ∧
      wagnerGraph.IsRegularOfDegree 3 ∧ wagnerGraph.CliqueFree 3 ∧
      ∃ x : ConfigSpace wagnerGraph,
        (∀ u, x.1 u 2 = 0) ∧ malkounAmplitude wagnerGraph x = 0 := by
  rcases Matematyka.MalkounWagnerCounterexample.exists_wagnerPath_zero with ⟨t₀, _, ht₀⟩
  exact wagner_bridge wagnerGraph_eq Matematyka.MalkounWagnerCounterexample.instDecidableRelWagner
    Matematyka.MalkounWagnerCounterexample.wagnerGraph_connected
    Matematyka.MalkounWagnerCounterexample.wagnerGraph_threeVertexConnected
    Matematyka.MalkounWagnerCounterexample.wagnerGraph_isRegularOfDegree_three
    Matematyka.MalkounWagnerCounterexample.wagnerGraph_cliqueFree_three
    (Matematyka.MalkounWagnerCounterexample.wagnerPath t₀)
    (Matematyka.MalkounWagnerCounterexample.wagnerPath_planar t₀)
    ht₀

/-- Disproof of General Conjecture D, proved in `Solution` via a rank-3 matrix on `C_6`. -/
theorem disproof_malkoun_conjecture_D : ¬ MalkounConjectureDProp := by
  intro hD
  apply Matematyka.MalkounConjectureD.disproof_malkoun_conjecture_D
  intro E V₁ V₂ instF instD κ₁ κ₂ H hpsd
  exact hD E V₁ V₂ κ₁ κ₂ H hpsd

/-- Disproof of Rank-2 Spinor Conjecture D, proved in `Solution` via a `2 × 12` matrix on `C_12`. -/
theorem disproof_malkoun_rank2_conjecture_D : ¬ MalkounRank2ConjectureDProp := by
  intro hR2
  apply Matematyka.MalkounConjectureD.disproof_malkoun_rank2_conjecture_D
  intro E V₁ V₂ instF instD κ₁ κ₂ B
  exact hR2 E V₁ V₂ κ₁ κ₂ B

/-- Disproof of Conjecture C on finite trees, proved in `Solution` via `cherryTree10` ($T_{10}$). -/
theorem disproof_malkoun_conjecture_C : ¬ MalkounConjectureCProp := by
  intro hC
  apply Matematyka.MalkounConjectureC.disproof_malkoun_conjecture_C
  intro n T inst hT x
  exact hC n T inst hT x

/-- Disproof of Conjecture A restricted to planar point configurations (`∀ u, x.1 u 2 = 0`) on
finite trees, proved on the explicit 10-vertex cubic cherry tree `cherryTree10` ($T_{10}$). -/
theorem disproof_malkoun_tree_conjecture_A :
    cherryTree10.IsTree ∧ ∃ x : ConfigSpace cherryTree10,
      Function.Injective x.1 ∧ (∀ u, x.1 u 2 = 0) ∧ malkounAmplitude cherryTree10 x = 0 :=
  cherry10_bridge cherryTree10_eq Matematyka.MalkounConjectureC.instDecidableRelCherry10
    Matematyka.MalkounConjectureC.cherryTree10_isTree
    Matematyka.MalkounConjectureC.cherryPinwheelConfig
    Matematyka.MalkounConjectureC.cherryPinwheelPts_injective
    Matematyka.MalkounConjectureC.cherryPinwheel_planar
    Matematyka.MalkounConjectureC.malkounAmplitude_cherryPinwheel_eq_zero

/-- Disproof of Conjecture C restricted to linear path graphs: on the explicit 15-vertex path
`pathGraphN 15` ($LG_{15}$), there exists `x ∈ C_{LG_15}(ℝ³)` with exact negative rational real
part `-40605770611892600000 / 58001564658819600000 < 0`. -/
theorem disproof_malkoun_path_conjecture_C_neg_re :
    ∃ x : ConfigSpace (pathGraphN 15),
      (malkounAmplitude (pathGraphN 15) x).re =
        (-40605770611892600000 : ℝ) / 58001564658819600000 ∧
      (malkounAmplitude (pathGraphN 15) x).re < 0 :=
  lg15_bridge pathGraphN15_eq Matematyka.MalkounConjectureC.instDecidableRelPath15
    Matematyka.MalkounConjectureC.lg15NegConfig
    Matematyka.MalkounConjectureC.malkounAmplitude_lg15Neg_re_eq

/-- Unconditional Path Conjecture B for all $n \in \mathbb{N}$: $|\mathcal{A}_{LG_n}(\mathbf{x})| \ge 1$. -/
theorem malkounAmplitude_pathGraphN_norm_ge_one (n : ℕ) (x : ConfigSpace (pathGraphN n)) :
    1 ≤ ‖malkounAmplitude (pathGraphN n) x‖ := by
  rw [malkounAmplitude_eq_mat (pathGraphN n) (instDecidableRelPathN n) x]
  change 1 ≤ ‖@Matematyka.MalkounCounterexample.malkounAmplitude n
      (Matematyka.MalkounPathPositivity.pathGraphN n)
      (Matematyka.MalkounPathPositivity.instDecidableRelPathN n) x‖
  exact Matematyka.MalkounPathPositivity.malkounAmplitude_pathGraphN_norm_ge_one n x

/-- Unconditional Planar Path Conjecture C for all $n \in \mathbb{N}$: $\operatorname{Re}(\mathcal{A}_{LG_n}(\mathbf{x})) \ge 1$. -/
theorem malkounAmplitude_pathGraphN_planar_re_ge_one (n : ℕ) (x : ConfigSpace (pathGraphN n))
    (hplanar : ∀ u, x.1 u 2 = 0) :
    1 ≤ (malkounAmplitude (pathGraphN n) x).re := by
  rw [malkounAmplitude_eq_mat (pathGraphN n) (instDecidableRelPathN n) x]
  change 1 ≤ (@Matematyka.MalkounCounterexample.malkounAmplitude n
      (Matematyka.MalkounPathPositivity.pathGraphN n)
      (Matematyka.MalkounPathPositivity.instDecidableRelPathN n) x).re
  exact Matematyka.MalkounPathPositivity.malkounAmplitude_pathGraphN_planar_re_ge_one n x hplanar

end Challenge
