import Matematyka.MalkounCounterexample

/-!
# Bipartite Gram-Matrix Reduction for Malkoun's $G$-Amplitude

We extend Malkoun's Theorem 4.1 (`arXiv:2508.13472v3`, Section 4 — proved there for trees)
to **all finite simple bipartite graphs** $G$.

Specifically, for any bipartition `part : Fin n → Bool` of `G` and any `x : ConfigSpace G`:
1. Using Malkoun's time-reversal operator `jTilde` (Eq. (22)), we prove
   `malkounAmplitude G x = starRingEnd ℂ (∑ σ₁ : bipP1 G part, ∑ σ₂ : bipP2 G part,
      ∏ e : BipEdge G part, bipGramMatrix G part x (σ₁.1 e) (σ₂.1 e))`,
   where `bipGramMatrix G part x = Bᴴ * B` is Hermitian positive semidefinite with unit diagonal,
   and `bipP1`, `bipP2` are the two edge-partition permutation subgroups whose intersection is trivial
   (`bipP1 ⊓ bipP2 = ⊥`, so `|P₁ ∩ P₂| = 1`).
2. Consequently, Malkoun's matrix-analytic Conjecture D implies `Re (malkounAmplitude G x) ≥ 1`
   (and hence Conjectures A, B, and C/Section 6) for **every** finite simple bipartite graph `G`.
-/

namespace Matematyka.MalkounBipartite

open Complex Classical ComplexOrder Matematyka.MalkounCounterexample

private lemma fin2_eq_zero_or_one (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

/-! ### Time-Reversal Spinor Map `jTilde` (Malkoun Eq. (22)) -/

/-- Complex anti-linear quaternionic / time-reversal map $\tilde{j}(u, v) = (-\bar{v}, \bar{u})$. -/
def jTilde (φ : Fin 2 → ℂ) : Fin 2 → ℂ
  | 0 => -starRingEnd ℂ (φ 1)
  | 1 => starRingEnd ℂ (φ 0)

lemma isPosSpinor_neg_jTilde {v : Fin 3 → ℝ} {φ : Fin 2 → ℂ} (h : IsPosSpinor v φ) :
    IsPosSpinor (fun k => -v k) (jTilde φ) := by
  refine ⟨?_, ?_⟩
  · simp only [jTilde, norm_neg, Complex.norm_conj, add_comm]
    exact h.1
  · have hm0 := congr_arg (starRingEnd ℂ) (congr_fun h.2 0)
    have hm1 := congr_arg (starRingEnd ℂ) (congr_fun h.2 1)
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub, map_mul,
      map_neg, Complex.conj_ofReal, Complex.conj_I] at hm0 hm1
    ext k
    rcases fin2_eq_zero_or_one k with rfl | rfl
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, jTilde, Complex.ofReal_neg]
      linear_combination -hm1
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, jTilde, Complex.ofReal_neg]
      linear_combination hm0

/-- Malkoun Eq. (22): $\omega(\psi, \tilde{j}\phi) = \overline{\langle \psi, \phi \rangle}$. -/
lemma omega_jTilde_right (ψ φ : Fin 2 → ℂ) :
    omega ψ (jTilde φ) =
      starRingEnd ℂ (starRingEnd ℂ (ψ 0) * φ 0 + starRingEnd ℂ (ψ 1) * φ 1) := by
  simp only [omega, jTilde, map_add, map_mul, Complex.conj_conj]
  ring

lemma omega_self_jTilde {ψ : Fin 2 → ℂ} (hnorm : ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1) :
    omega ψ (jTilde ψ) = 1 := by
  have hsq : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc omega ψ (jTilde ψ)
      = ψ 0 * starRingEnd ℂ (ψ 0) + ψ 1 * starRingEnd ℂ (ψ 1) := by simp [omega, jTilde]
    _ = ((‖ψ 0‖ ^ 2 : ℝ) : ℂ) + ((‖ψ 1‖ ^ 2 : ℝ) : ℂ) := by rw [hsq (ψ 0), hsq (ψ 1)]
    _ = ((‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    _ = 1 := by rw [hnorm, Complex.ofReal_one]

/-! ### Bipartite Edge Set, Partition Subgroups $P_1, P_2$, and Gram Matrix -/

/-- Explicit 2-coloring witness of bipartiteness for a finite simple graph. -/
def IsBipartite {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool) : Prop :=
  ∀ u v, G.Adj u v → part u ≠ part v

/-- Directed edges oriented from the `false` part to the `true` part. -/
abbrev BipEdge {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool) :=
  { e : Fin n × Fin n // G.Adj e.1 e.2 ∧ part e.1 = false ∧ part e.2 = true }

private def bipOriEquiv {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (hb : IsBipartite G part) : BipEdge G part ≃ OriEdge G where
  toFun e :=
    if h : e.1.1 < e.1.2 then ⟨e.1, e.2.1, h⟩
    else ⟨(e.1.2, e.1.1), e.2.1.symm, lt_of_le_of_ne (not_lt.mp h) (G.ne_of_adj e.2.1).symm⟩
  invFun e :=
    if hf : part e.1.1 = false then
      ⟨e.1, e.2.1, hf, Bool.eq_true_of_not_eq_false fun ht =>
        hb e.1.1 e.1.2 e.2.1 (hf.trans ht.symm)⟩
    else
      have ht : part e.1.1 = true := Bool.eq_true_of_not_eq_false hf
      have hf2 : part e.1.2 = false := Bool.eq_false_of_not_eq_true fun h2 =>
        hb e.1.1 e.1.2 e.2.1 (ht.trans h2.symm)
      ⟨(e.1.2, e.1.1), e.2.1.symm, hf2, ht⟩
  left_inv e := by
    apply Subtype.ext
    rcases e with ⟨⟨u, w⟩, hadj, hu, hw⟩
    by_cases h : u < w
    · simp [h, hu]
    · have hf : part w ≠ false := by rw [hw]; decide
      simp [h, hf]
  right_inv e := by
    apply Subtype.ext
    rcases e with ⟨⟨u, w⟩, hadj, hlt⟩
    by_cases hf : part u = false
    · simp [hf, hlt]
    · simp [hf, not_lt_of_gt hlt]

/-- Spinors on `BipEdge G part` (false → true). -/
noncomputable def bipEdgeSpinor {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    (x : ConfigSpace G) (e : BipEdge G part) : Fin 2 → ℂ :=
  canonicalSpinor (unitDir (x.1 e.1.1) (x.1 e.1.2))

/-- Bipartite choice of $+1$-eigenvector family: `canonicalSpinor` on `false → true`,
`jTilde` of opposite direction on `true → false`. -/
noncomputable def bipSpinorFamily {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (x : ConfigSpace G) (p q : Fin n) : Fin 2 → ℂ :=
  if part p = false then canonicalSpinor (unitDir (x.1 p) (x.1 q))
  else jTilde (canonicalSpinor (unitDir (x.1 q) (x.1 p)))

lemma isPosSpinor_bipSpinorFamily {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (x : ConfigSpace G) (u w : Fin n) (hadj : G.Adj u w) :
    IsPosSpinor (unitDir (x.1 u) (x.1 w)) (bipSpinorFamily G part x u w) := by
  by_cases hu : part u = false
  · simp only [bipSpinorFamily, hu, ↓reduceIte]
    exact isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 u w hadj))
  · simp only [bipSpinorFamily, hu]
    have hbase := isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 w u hadj.symm))
    have hneg := isPosSpinor_neg_jTilde hbase
    have hdir : (fun k => -unitDir (x.1 w) (x.1 u) k) = unitDir (x.1 u) (x.1 w) := by
      funext k
      rw [unitDir_swap]
      ring
    rwa [hdir] at hneg

/-- Subgroup of permutations of `E` preserving equivalence classes induced by `κ : E → V`. -/
def partitionSubgroup {E V : Type*} (κ : E → V) : Subgroup (Equiv.Perm E) where
  carrier := { σ | ∀ e, κ (σ e) = κ e }
  one_mem' _ := rfl
  mul_mem' {a b} h1 h2 e := by
    change κ (a (b e)) = κ e
    rw [h1, h2]
  inv_mem' {a} h e := by
    change κ (a⁻¹ e) = κ e
    have ha := (h (a⁻¹ e)).symm
    have he : a (a⁻¹ e) = e := congrArg (fun g : Equiv.Perm E => g e) (mul_inv_cancel a)
    rwa [he] at ha

/-- Equivalence-preserving subgroup fixing the `false`-endpoint of every bipartite edge. -/
def bipP1 {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool) :
    Subgroup (Equiv.Perm (BipEdge G part)) :=
  partitionSubgroup (fun e => e.1.1)

/-- Equivalence-preserving subgroup fixing the `true`-endpoint of every bipartite edge. -/
def bipP2 {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool) :
    Subgroup (Equiv.Perm (BipEdge G part)) :=
  partitionSubgroup (fun e => e.1.2)

@[simp] private lemma bipP1_fst {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    {τ : Equiv.Perm (BipEdge G part)} (hτ : τ ∈ bipP1 G part) (e : BipEdge G part) :
    (τ e).1.1 = e.1.1 :=
  hτ e

@[simp] private lemma bipP2_snd {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    {τ : Equiv.Perm (BipEdge G part)} (hτ : τ ∈ bipP2 G part) (e : BipEdge G part) :
    (τ e).1.2 = e.1.2 :=
  hτ e

/-- Since $G$ is a simple graph, no two distinct edges share both endpoints: `P₁ ⊓ P₂ = ⊥`. -/
theorem bipP1_inf_bipP2_eq_bot {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool) :
    bipP1 G part ⊓ bipP2 G part = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ ⟨h1, h2⟩
  ext e
  · exact congrArg Fin.val (h1 e)
  · exact congrArg Fin.val (h2 e)

private lemma card_bipP1_inf_bipP2 {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    [Fintype ↥(bipP1 G part ⊓ bipP2 G part)] :
    Fintype.card ↥(bipP1 G part ⊓ bipP2 G part) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, fun y => Subtype.ext ?_⟩
  have hy : y.1 ∈ (⊥ : Subgroup (Equiv.Perm (BipEdge G part))) :=
    (bipP1_inf_bipP2_eq_bot G part) ▸ y.2
  exact Subgroup.mem_bot.mp hy

private def mkBipFalse {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    (hb : IsBipartite G part) {u w : Fin n} (hu : part u = false) (hadj : G.Adj u w) :
    BipEdge G part :=
  ⟨(u, w), hadj, hu, Bool.eq_true_of_not_eq_false fun h => hb u w hadj (hu.trans h.symm)⟩

private def mkBipTrue {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    (hb : IsBipartite G part) {u w : Fin n} (hu : part u = true) (hadj : G.Adj u w) :
    BipEdge G part :=
  ⟨(w, u), hadj.symm, Bool.eq_false_of_not_eq_true fun h => hb u w hadj (hu.trans h.symm), hu⟩

private lemma bipP1_mkFalse {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    (hb : IsBipartite G part) (τ : Equiv.Perm (BipEdge G part)) (hτ : τ ∈ bipP1 G part)
    (e : BipEdge G part) :
    mkBipFalse hb e.2.2.1 (by have h := (τ e).2.1; rwa [bipP1_fst hτ e] at h) = τ e := by
  apply Subtype.ext
  apply Prod.ext
  · exact (bipP1_fst hτ e).symm
  · rfl

private lemma bipP2_mkTrue {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    (hb : IsBipartite G part) (τ : Equiv.Perm (BipEdge G part)) (hτ : τ ∈ bipP2 G part)
    (e : BipEdge G part) :
    mkBipTrue hb e.2.2.2 (by have h := (τ e).2.1.symm; rwa [bipP2_snd hτ e] at h) = τ e := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (bipP2_snd hτ e).symm

private def bipPermToSource {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (hb : IsBipartite G part) (p : bipP1 G part × bipP2 G part) : SourcePerm G :=
  fun u =>
    if hu : part u = false then
      { toFun := fun w =>
          let e := mkBipFalse hb hu w.2
          ⟨(p.1.1 e).1.2, by have h := (p.1.1 e).2.1; rwa [bipP1_fst p.1.2 e] at h⟩
        invFun := fun w =>
          let e := mkBipFalse hb hu w.2
          ⟨(p.1.1⁻¹ e).1.2, by have h := (p.1.1⁻¹ e).2.1; rwa [bipP1_fst ((bipP1 G part).inv_mem p.1.2) e] at h⟩
        left_inv := fun w => by
          apply Subtype.ext
          dsimp only
          have heq := bipP1_mkFalse hb p.1.1 p.1.2 (mkBipFalse hb hu w.2)
          have h := congrArg (fun z : BipEdge G part => (p.1.1⁻¹ z).1.2) heq
          simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h
          exact h
        right_inv := fun w => by
          apply Subtype.ext
          dsimp only
          have heq := bipP1_mkFalse hb p.1.1⁻¹ ((bipP1 G part).inv_mem p.1.2) (mkBipFalse hb hu w.2)
          have h := congrArg (fun z : BipEdge G part => (p.1.1 z).1.2) heq
          simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
          exact h }
    else
      have ht : part u = true := Bool.eq_true_of_not_eq_false hu
      { toFun := fun w =>
          let e := mkBipTrue hb ht w.2
          ⟨(p.2.1 e).1.1, by have h := (p.2.1 e).2.1.symm; rwa [bipP2_snd p.2.2 e] at h⟩
        invFun := fun w =>
          let e := mkBipTrue hb ht w.2
          ⟨(p.2.1⁻¹ e).1.1, by have h := (p.2.1⁻¹ e).2.1.symm; rwa [bipP2_snd ((bipP2 G part).inv_mem p.2.2) e] at h⟩
        left_inv := fun w => by
          apply Subtype.ext
          dsimp only
          have heq := bipP2_mkTrue hb p.2.1 p.2.2 (mkBipTrue hb ht w.2)
          have h := congrArg (fun z : BipEdge G part => (p.2.1⁻¹ z).1.1) heq
          simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h
          exact h
        right_inv := fun w => by
          apply Subtype.ext
          dsimp only
          have heq := bipP2_mkTrue hb p.2.1⁻¹ ((bipP2 G part).inv_mem p.2.2) (mkBipTrue hb ht w.2)
          have h := congrArg (fun z : BipEdge G part => (p.2.1 z).1.1) heq
          simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
          exact h }

private def bipSourceToPerm {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (hb : IsBipartite G part) (σ : SourcePerm G) : bipP1 G part × bipP2 G part :=
  ( ⟨ { toFun := fun e => mkBipFalse hb e.2.2.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).2
        invFun := fun e => mkBipFalse hb e.2.2.1 ((σ e.1.1)⁻¹ ⟨e.1.2, e.2.1⟩).2
        left_inv := fun e => by
          apply Subtype.ext
          dsimp only [mkBipFalse]
          apply Prod.ext
          · rfl
          · exact congrArg Subtype.val ((σ e.1.1).symm_apply_apply ⟨e.1.2, e.2.1⟩)
        right_inv := fun e => by
          apply Subtype.ext
          dsimp only [mkBipFalse]
          apply Prod.ext
          · rfl
          · exact congrArg Subtype.val ((σ e.1.1).apply_symm_apply ⟨e.1.2, e.2.1⟩) },
      fun _ => rfl ⟩,
    ⟨ { toFun := fun e => mkBipTrue hb e.2.2.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).2
        invFun := fun e => mkBipTrue hb e.2.2.2 ((σ e.1.2)⁻¹ ⟨e.1.1, e.2.1.symm⟩).2
        left_inv := fun e => by
          apply Subtype.ext
          dsimp only [mkBipTrue]
          apply Prod.ext
          · exact congrArg Subtype.val ((σ e.1.2).symm_apply_apply ⟨e.1.1, e.2.1.symm⟩)
          · rfl
        right_inv := fun e => by
          apply Subtype.ext
          dsimp only [mkBipTrue]
          apply Prod.ext
          · exact congrArg Subtype.val ((σ e.1.2).apply_symm_apply ⟨e.1.1, e.2.1.symm⟩)
          · rfl },
      fun _ => rfl ⟩ )

private def bipSourcePermEquiv {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (hb : IsBipartite G part) : (bipP1 G part × bipP2 G part) ≃ SourcePerm G where
  toFun := bipPermToSource G part hb
  invFun := bipSourceToPerm G part hb
  left_inv p := by
    rcases p with ⟨τ1, τ2⟩
    apply Prod.ext
    · apply Subtype.ext
      exact Equiv.ext fun e => Subtype.ext (Prod.ext
        (by
          have h1 : (τ1.1 e).1.1 = e.1.1 := τ1.2 e
          simp only [bipSourceToPerm, bipPermToSource, Equiv.coe_fn_mk, mkBipFalse,
            e.2.2.1, ↓reduceDIte]
          exact h1.symm)
        (by simp [bipSourceToPerm, bipPermToSource, mkBipFalse, e.2.2.1]))
    · apply Subtype.ext
      exact Equiv.ext fun e => Subtype.ext (Prod.ext
        (by
          have ht : part e.1.2 ≠ false := by rw [e.2.2.2]; decide
          simp [bipSourceToPerm, bipPermToSource, mkBipTrue, ht])
        (by
          have h2 : (τ2.1 e).1.2 = e.1.2 := τ2.2 e
          have ht : part e.1.2 ≠ false := by rw [e.2.2.2]; decide
          simp only [bipSourceToPerm, bipPermToSource, Equiv.coe_fn_mk, mkBipTrue, ht]
          exact h2.symm))
  right_inv σ := by
    funext u
    exact Equiv.ext fun ⟨w, hw⟩ => Subtype.ext (by
      by_cases hu : part u = false
      · simp [bipPermToSource, bipSourceToPerm, mkBipFalse, hu]
      · simp [bipPermToSource, bipSourceToPerm, mkBipTrue, hu])

private lemma bipPermToSource_false_apply {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    (hb : IsBipartite G part) (τ₁ : bipP1 G part) (τ₂ : bipP2 G part)
    (e : BipEdge G part) :
    (bipPermToSource G part hb (τ₁, τ₂) e.1.1 ⟨e.1.2, e.2.1⟩).1 = (τ₁.1 e).1.2 := by
  simp [bipPermToSource, mkBipFalse, e.2.2.1]

private lemma bipPermToSource_true_apply {n : ℕ} {G : SimpleGraph (Fin n)} {part : Fin n → Bool}
    (hb : IsBipartite G part) (τ₁ : bipP1 G part) (τ₂ : bipP2 G part)
    (e : BipEdge G part) :
    (bipPermToSource G part hb (τ₁, τ₂) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1 = (τ₂.1 e).1.1 := by
  have ht : part e.1.2 ≠ false := by rw [e.2.2.2]; decide
  simp [bipPermToSource, mkBipTrue, ht]

/-- Gram matrix $H_{a,b} = \langle \psi_a, \psi_b \rangle$ of the bipartite edge spinors. -/
noncomputable def bipGramMatrix {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (x : ConfigSpace G) : Matrix (BipEdge G part) (BipEdge G part) ℂ :=
  fun a b =>
    starRingEnd ℂ (bipEdgeSpinor x a 0) * bipEdgeSpinor x b 0 +
    starRingEnd ℂ (bipEdgeSpinor x a 1) * bipEdgeSpinor x b 1

private noncomputable def bipSpinorMatrix {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (x : ConfigSpace G) : Matrix (Fin 2) (BipEdge G part) ℂ :=
  fun k e => bipEdgeSpinor x e k

private lemma bipGramMatrix_eq_conjTranspose_mul {n : ℕ} (G : SimpleGraph (Fin n))
    (part : Fin n → Bool) (x : ConfigSpace G) :
    bipGramMatrix G part x = (bipSpinorMatrix G part x).conjTranspose * bipSpinorMatrix G part x := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, bipSpinorMatrix, bipGramMatrix,
    Fin.sum_univ_two, Complex.star_def]

theorem bipGramMatrix_posSemidef {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (x : ConfigSpace G) : (bipGramMatrix G part x).PosSemidef := by
  rw [bipGramMatrix_eq_conjTranspose_mul]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem bipGramMatrix_isHermitian {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (x : ConfigSpace G) : (bipGramMatrix G part x).IsHermitian :=
  (bipGramMatrix_posSemidef G part x).isHermitian

theorem bipGramMatrix_diag_eq_one {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (x : ConfigSpace G) (e : BipEdge G part) :
    bipGramMatrix G part x e e = 1 := by
  have hspin : IsPosSpinor (unitDir (x.1 e.1.1) (x.1 e.1.2)) (bipEdgeSpinor x e) :=
    isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 e.1.1 e.1.2 e.2.1))
  have hc := congr_arg (starRingEnd ℂ) (omega_self_jTilde hspin.1)
  rw [omega_jTilde_right, Complex.conj_conj] at hc
  simpa [bipGramMatrix] using hc

/-! ### Bipartite Gram Reduction & Extension of Malkoun Theorem 4.1 -/

/-- Matrix-analytic **Conjecture D** of Malkoun (`arXiv:2508.13472v3`, Section 4):
for every finite index set `E`, two partition-induced subgroups `P₁, P₂` of `Equiv.Perm E`,
and every Hermitian positive semidefinite matrix `H` on `E`,
$\operatorname{Re}(f_{\sim_1, \sim_2}(H)) \ge |P_1 \cap P_2| \prod_{e \in E} \operatorname{Re}(H_{ee})$. -/
def MalkounConjectureDProp : Prop :=
  ∀ (E V₁ V₂ : Type) [Fintype E] [DecidableEq E] (κ₁ : E → V₁) (κ₂ : E → V₂)
    (H : Matrix E E ℂ),
    H.PosSemidef →
    (∑ σ₁ : partitionSubgroup κ₁, ∑ σ₂ : partitionSubgroup κ₂,
      ∏ e : E, H (σ₁.1 e) (σ₂.1 e)).re ≥
      (Fintype.card ↥(partitionSubgroup κ₁ ⊓ partitionSubgroup κ₂) : ℝ) *
        ∏ e : E, (H e e).re

private lemma prod_term_bipOriEquiv {n : ℕ} (G : SimpleGraph (Fin n)) (part : Fin n → Bool)
    (hb : IsBipartite G part) (ψ : Fin n → Fin n → Fin 2 → ℂ) (σ : SourcePerm G)
    (e : BipEdge G part) :
    omega (ψ (bipOriEquiv G part hb e).1.1
             (σ (bipOriEquiv G part hb e).1.1 ⟨(bipOriEquiv G part hb e).1.2, (bipOriEquiv G part hb e).2.1⟩).1)
          (ψ (bipOriEquiv G part hb e).1.2
             (σ (bipOriEquiv G part hb e).1.2 ⟨(bipOriEquiv G part hb e).1.1, (bipOriEquiv G part hb e).2.1.symm⟩).1) =
      (if e.1.1 < e.1.2 then (1 : ℂ) else -1) *
        omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)
              (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) := by
  by_cases hlt : e.1.1 < e.1.2
  · have he : bipOriEquiv G part hb e = ⟨e.1, e.2.1, hlt⟩ := by
      simp [bipOriEquiv, hlt]
    rw [he]
    simp [hlt]
  · have hgt : e.1.2 < e.1.1 := lt_of_le_of_ne (not_lt.mp hlt) (G.ne_of_adj e.2.1).symm
    have he : bipOriEquiv G part hb e = ⟨(e.1.2, e.1.1), e.2.1.symm, hgt⟩ := by
      simp [bipOriEquiv, hlt]
    rw [he]
    simp only [hlt, ↓reduceIte]
    rw [omega_swap]
    ring

/-- **Bipartite Gram Reduction Theorem:**
For every finite simple bipartite graph `(G, part)` and every `x : ConfigSpace G`,
$\mathcal{A}_G(\mathbf{x}) = \overline{f_{\sim_1, \sim_2}(H)}$, where $H = B^H B \succeq 0$
with unit diagonal and $|P_1 \cap P_2| = 1$. -/
theorem malkounAmplitude_bipartite_eq_conj_gram {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (part : Fin n → Bool) (hb : IsBipartite G part) (x : ConfigSpace G) :
    malkounAmplitude G x =
      starRingEnd ℂ (∑ σ₁ : bipP1 G part, ∑ σ₂ : bipP2 G part,
        ∏ e : BipEdge G part, bipGramMatrix G part x (σ₁.1 e) (σ₂.1 e)) := by
  let ψ := bipSpinorFamily G part x
  have hamp : malkounAmplitude G x = malkounAmplitudeOfSpinors G ψ :=
    (malkounAmplitude_eq_of_isPosSpinor G x ψ (fun u w hadj =>
      isPosSpinor_bipSpinorFamily G part x u w hadj)).symm
  rw [hamp, malkounAmplitudeOfSpinors]
  let S : ℂ := ∏ e : BipEdge G part, if e.1.1 < e.1.2 then (1 : ℂ) else -1
  have hS : S ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ => by split_ifs <;> norm_num
  have hden : malkounDen G ψ = S := by
    unfold malkounDen
    rw [← Fintype.prod_equiv (bipOriEquiv G part hb)
      (fun e => omega (ψ (bipOriEquiv G part hb e).1.1 (bipOriEquiv G part hb e).1.2)
                      (ψ (bipOriEquiv G part hb e).1.2 (bipOriEquiv G part hb e).1.1))
      (fun e => omega (ψ e.1.1 e.1.2) (ψ e.1.2 e.1.1)) (fun _ => rfl)]
    refine Finset.prod_congr rfl fun e _ => ?_
    have hnorm : ‖bipEdgeSpinor x e 0‖ ^ 2 + ‖bipEdgeSpinor x e 1‖ ^ 2 = 1 :=
      (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 e.1.1 e.1.2 e.2.1))).1
    have hfalse : ψ e.1.1 e.1.2 = bipEdgeSpinor x e := by
      simp [ψ, bipSpinorFamily, bipEdgeSpinor, e.2.2.1]
    have htrue : ψ e.1.2 e.1.1 = jTilde (bipEdgeSpinor x e) := by
      have ht : part e.1.2 ≠ false := by rw [e.2.2.2]; decide
      simp [ψ, bipSpinorFamily, bipEdgeSpinor, ht]
    by_cases hlt : e.1.1 < e.1.2
    · simp only [bipOriEquiv, Equiv.coe_fn_mk, hlt, ↓reduceDIte, hfalse, htrue]
      rw [omega_self_jTilde hnorm]
      simp
    · simp only [bipOriEquiv, Equiv.coe_fn_mk, hlt, ↓reduceDIte, hfalse, htrue]
      rw [omega_swap, omega_self_jTilde hnorm]
      simp
  have hnum : malkounNum G ψ = S * starRingEnd ℂ
      (∑ σ₁ : bipP1 G part, ∑ σ₂ : bipP2 G part,
        ∏ e : BipEdge G part, bipGramMatrix G part x (σ₁.1 e) (σ₂.1 e)) := by
    unfold malkounNum
    rw [← Fintype.sum_equiv (bipSourcePermEquiv G part hb)
      (fun p => ∏ e : OriEdge G,
        omega (ψ e.1.1 ((bipPermToSource G part hb p) e.1.1 ⟨e.1.2, e.2.1⟩).1)
              (ψ e.1.2 ((bipPermToSource G part hb p) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
      (fun σ => ∏ e : OriEdge G,
        omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ₁ _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ₂ _ => ?_
    rw [← Fintype.prod_equiv (bipOriEquiv G part hb)
      (fun e =>
        let σ := bipPermToSource G part hb (σ₁, σ₂)
        (if e.1.1 < e.1.2 then (1 : ℂ) else -1) *
          omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)
                (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
      (fun e =>
        let σ := bipPermToSource G part hb (σ₁, σ₂)
        omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
      (fun e => (prod_term_bipOriEquiv G part hb ψ (bipPermToSource G part hb (σ₁, σ₂)) e).symm)]
    rw [Finset.prod_mul_distrib, map_prod]
    refine congrArg (S * ·) (Finset.prod_congr rfl fun e _ => ?_)
    have hp1 : ψ e.1.1 ((bipPermToSource G part hb (σ₁, σ₂)) e.1.1 ⟨e.1.2, e.2.1⟩).1 =
        bipEdgeSpinor x (σ₁.1 e) := by
      rw [bipPermToSource_false_apply hb σ₁ σ₂ e]
      have h1 : (σ₁.1 e).1.1 = e.1.1 := σ₁.2 e
      simp [ψ, bipSpinorFamily, bipEdgeSpinor, e.2.2.1, h1]
    have hp2 : ψ e.1.2 ((bipPermToSource G part hb (σ₁, σ₂)) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1 =
        jTilde (bipEdgeSpinor x (σ₂.1 e)) := by
      rw [bipPermToSource_true_apply hb σ₁ σ₂ e]
      have ht : part e.1.2 ≠ false := by rw [e.2.2.2]; decide
      have h2 : (σ₂.1 e).1.2 = e.1.2 := σ₂.2 e
      simp [ψ, bipSpinorFamily, bipEdgeSpinor, ht, h2]
    rw [hp1, hp2, omega_jTilde_right]
    rfl
  rw [hnum, hden, mul_div_cancel_left₀ _ hS]

/-- **Extension of Malkoun Theorem 4.1 (`arXiv:2508.13472v3`):**
If Conjecture D holds, then **every** finite simple bipartite graph $G$ obeys
$\operatorname{Re}(\mathcal{A}_G(\mathbf{x})) \ge 1$ (and hence $|\mathcal{A}_G(\mathbf{x})| \ge 1$,
$\mathcal{A}_G(\mathbf{x}) \ne 0$) for all $\mathbf{x} \in C_G(\mathbb{R}^3)$. -/
theorem conjectureD_implies_bipartite_re_ge_one (hD : MalkounConjectureDProp)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (part : Fin n → Bool) (hb : IsBipartite G part) (x : ConfigSpace G) :
    1 ≤ (malkounAmplitude G x).re := by
  rw [malkounAmplitude_bipartite_eq_conj_gram G part hb x, Complex.conj_re]
  have hpsd := bipGramMatrix_posSemidef G part x
  have hineq := hD (BipEdge G part) (Fin n) (Fin n)
    (fun e => e.1.1) (fun e => e.1.2) (bipGramMatrix G part x) hpsd
  have hcard : ∀ [inst : Fintype ↥(bipP1 G part ⊓ bipP2 G part)],
      @Fintype.card ↥(bipP1 G part ⊓ bipP2 G part) inst = 1 :=
    fun {_} => card_bipP1_inf_bipP2 G part
  have hdiag : ∀ e : BipEdge G part, (bipGramMatrix G part x e e).re = 1 := fun e => by
    rw [bipGramMatrix_diag_eq_one, Complex.one_re]
  rw [show partitionSubgroup (fun e : BipEdge G part => e.1.1) = bipP1 G part from rfl,
      show partitionSubgroup (fun e : BipEdge G part => e.1.2) = bipP2 G part from rfl] at hineq
  rw [hcard, Nat.cast_one, one_mul, Finset.prod_eq_one (fun e _ => hdiag e)] at hineq
  convert hineq

theorem conjectureD_implies_bipartite_abs_ge_one_and_ne_zero (hD : MalkounConjectureDProp)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (part : Fin n → Bool) (hb : IsBipartite G part) (x : ConfigSpace G) :
    1 ≤ ‖malkounAmplitude G x‖ ∧ malkounAmplitude G x ≠ 0 := by
  have hre := conjectureD_implies_bipartite_re_ge_one hD G part hb x
  have hnorm : 1 ≤ ‖malkounAmplitude G x‖ := le_trans hre (Complex.re_le_norm _)
  refine ⟨hnorm, fun h0 => ?_⟩
  rw [h0, norm_zero] at hnorm
  linarith

end Matematyka.MalkounBipartite
