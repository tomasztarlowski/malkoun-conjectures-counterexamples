import Mathlib

/-!
# Formal Disproof of Malkoun's Conjectures A, B, and Connected-Graph Real-Part Bound

We formalize Malkoun's exact $G$-amplitude function $\mathcal{A}_G(\mathbf{x})$
from *Finite graphs and configurations of points* (`arXiv:2508.13472v3`, Sept 7, 2026)
for any finite simple graph `G : SimpleGraph (Fin n)` and construct an explicit
connected 8-vertex, 13-edge planar counterexample `barbellK4Graph` (two $K_4$ cliques
joined by a bridge) along a collision-free straight-line homotopy $\gamma(t)$ ($t \in [0, 1]$).
-/

namespace Matematyka.MalkounCounterexample

open Complex Real

section GeneralDefinitions

variable {n : ℕ}

/-- Configuration space $C_G(\mathbb{R}^3)$: adjacent vertices cannot collide. -/
def ConfigSpace (G : SimpleGraph (Fin n)) : Type :=
  { x : Fin n → Fin 3 → ℝ // ∀ u v, G.Adj u v → x u ≠ x v }

/-- Euclidean norm of a vector in $\mathbb{R}^3$. -/
noncomputable def euclidNorm (v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)

lemma euclidNorm_pos_of_ne {a b : Fin 3 → ℝ} (h : a ≠ b) :
    0 < euclidNorm (fun k => b k - a k) := by
  rw [euclidNorm, Real.sqrt_pos]
  by_contra hle
  push Not at hle
  have h0 : b 0 - a 0 = 0 := by
    nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1), sq_nonneg (b 2 - a 2)]
  have h1 : b 1 - a 1 = 0 := by
    nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1), sq_nonneg (b 2 - a 2)]
  have h2 : b 2 - a 2 = 0 := by
    nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1), sq_nonneg (b 2 - a 2)]
  apply h
  ext k
  fin_cases k <;> dsimp <;> linarith

/-- Unit direction vector $v_{ij} = (\mathbf{x}_j - \mathbf{x}_i) / \|\mathbf{x}_j - \mathbf{x}_i\| \in S^2$. -/
noncomputable def unitDir (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => (b k - a k) / euclidNorm (fun j => b j - a j)

lemma unitDir_norm_sq {a b : Fin 3 → ℝ} (h : a ≠ b) :
    (unitDir a b 0) ^ 2 + (unitDir a b 1) ^ 2 + (unitDir a b 2) ^ 2 = 1 := by
  have hpos : 0 < euclidNorm (fun j => b j - a j) := euclidNorm_pos_of_ne h
  have hne : euclidNorm (fun j => b j - a j) ≠ 0 := hpos.ne'
  have hsq : euclidNorm (fun j => b j - a j) ^ 2 =
      (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 + (b 2 - a 2) ^ 2 := by
    rw [euclidNorm, Real.sq_sqrt]
    positivity
  unfold unitDir
  field_simp [hne]
  linarith

lemma unitDir_swap (a b : Fin 3 → ℝ) :
    unitDir b a = fun k => -unitDir a b k := by
  ext k
  have hnorm : euclidNorm (fun j => a j - b j) = euclidNorm (fun j => b j - a j) := by
    simp only [euclidNorm]
    congr 1
    ring
  simp only [unitDir, hnorm]
  ring

/-- Hermitian $2 \times 2$ matrix $v \cdot \vec{\sigma}$. -/
def pauliDot (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 2 : ℂ), (v 0 : ℂ) - Complex.I * (v 1 : ℂ);
     (v 0 : ℂ) + Complex.I * (v 1 : ℂ), -(v 2 : ℂ)]

/-- Normalized $+1$-eigenvector of $v \cdot \vec{\sigma}$ (Malkoun Eq. (5)). -/
def IsPosSpinor (v : Fin 3 → ℝ) (ψ : Fin 2 → ℂ) : Prop :=
  ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1 ∧ (pauliDot v).mulVec ψ = ψ

/-- Skew-symmetric bilinear form $\omega$ on $\mathbb{C}^2$ (Malkoun Eq. (7)). -/
def omega (ψ φ : Fin 2 → ℂ) : ℂ :=
  ψ 0 * φ 1 - ψ 1 * φ 0

lemma omega_swap (ψ φ : Fin 2 → ℂ) : omega φ ψ = -omega ψ φ := by
  simp only [omega]; ring

lemma omega_smul (c₁ c₂ : ℂ) (ψ φ : Fin 2 → ℂ) :
    omega (fun k => c₁ * ψ k) (fun k => c₂ * φ k) = (c₁ * c₂) * omega ψ φ := by
  simp only [omega]; ring

lemma pauliDot_neg (v : Fin 3 → ℝ) :
    pauliDot (fun k => -v k) = -pauliDot v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliDot] <;> ring

/-- Any two $+1$-eigenvectors of `pauliDot v` satisfy `omega ψ φ = 0`. -/
lemma omega_eq_zero_of_mulVec {v : Fin 3 → ℝ} {ψ φ : Fin 2 → ℂ}
    (hψ : (pauliDot v).mulVec ψ = ψ) (hφ : (pauliDot v).mulVec φ = φ) :
    omega ψ φ = 0 := by
  have hψ0 := congr_fun hψ 0
  have hψ1 := congr_fun hψ 1
  have hφ0 := congr_fun hφ 0
  have hφ1 := congr_fun hφ 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] at hψ0 hψ1 hφ0 hφ1
  have hA : ((v 2 : ℂ) - 1) * omega ψ φ = 0 := by
    unfold omega
    linear_combination (φ 1) * hψ0 - (ψ 1) * hφ0
  have hB : (-(v 2 : ℂ) - 1) * omega ψ φ = 0 := by
    unfold omega
    linear_combination (ψ 0) * hφ1 - (φ 0) * hψ1
  have hsum : (-2 : ℂ) * omega ψ φ = 0 := by linear_combination hA + hB
  exact (mul_eq_zero.mp hsum).resolve_left (by norm_num)

/-- Any two normalized $+1$-eigenvectors of `pauliDot v` differ by a nonzero scalar factor. -/
lemma isPosSpinor_collinear {v : Fin 3 → ℝ} {ψ φ : Fin 2 → ℂ}
    (hψ : IsPosSpinor v ψ) (hφ : IsPosSpinor v φ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ k, φ k = c * ψ k := by
  have hom := omega_eq_zero_of_mulVec hψ.2 hφ.2
  have hψ_nz : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hn := hψ.1
    rw [h.1, h.2] at hn
    norm_num at hn
  have hφ_nz : φ 0 ≠ 0 ∨ φ 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hn := hφ.1
    rw [h.1, h.2] at hn
    norm_num at hn
  have heq : ψ 0 * φ 1 = ψ 1 * φ 0 := sub_eq_zero.mp hom
  rcases hψ_nz with h0 | h1
  · refine ⟨φ 0 / ψ 0, ?_, ?_⟩
    · intro hc
      have hφ0 : φ 0 = 0 := (div_eq_zero_iff.mp hc).resolve_right h0
      rw [hφ0, mul_zero] at heq
      have hφ1 : φ 1 = 0 := (mul_eq_zero.mp heq).resolve_left h0
      rcases hφ_nz with h' | h'
      · exact h' hφ0
      · exact h' hφ1
    · intro k
      fin_cases k <;> dsimp
      · field_simp [h0]
      · field_simp [h0]; linear_combination heq
  · refine ⟨φ 1 / ψ 1, ?_, ?_⟩
    · intro hc
      have hφ1 : φ 1 = 0 := (div_eq_zero_iff.mp hc).resolve_right h1
      rw [hφ1, mul_zero] at heq
      have hφ0 : φ 0 = 0 := (mul_eq_zero.mp heq.symm).resolve_left h1
      rcases hφ_nz with h' | h'
      · exact h' hφ0
      · exact h' hφ1
    · intro k
      fin_cases k <;> dsimp
      · field_simp [h1]; linear_combination -heq
      · field_simp [h1]

/-- A $+1$-eigenvector of $v\cdot\vec{\sigma}$ and a $+1$-eigenvector of $(-v)\cdot\vec{\sigma}$
never have vanishing $\omega$. -/
lemma omega_opp_ne_zero {v : Fin 3 → ℝ} {ψ φ : Fin 2 → ℂ}
    (hψ : IsPosSpinor v ψ) (hφ : IsPosSpinor (fun k => -v k) φ) :
    omega ψ φ ≠ 0 := by
  intro hom
  have hψ_nz : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra h; push Not at h; have hn := hψ.1; rw [h.1, h.2] at hn; norm_num at hn
  have hφ_nz : φ 0 ≠ 0 ∨ φ 1 ≠ 0 := by
    by_contra h; push Not at h; have hn := hφ.1; rw [h.1, h.2] at hn; norm_num at hn
  have heq : ψ 0 * φ 1 = ψ 1 * φ 0 := sub_eq_zero.mp hom
  have hφ_neg : (pauliDot v).mulVec φ = -φ := by
    have hneg : -(pauliDot v).mulVec φ = φ := by
      simpa [pauliDot_neg, Matrix.neg_mulVec] using hφ.2
    ext k
    have hk := congr_fun hneg k
    simp only [Pi.neg_apply] at hk ⊢
    linear_combination -hk
  have hmul : (pauliDot v).mulVec φ = φ := by
    rcases hψ_nz with h0 | h1
    · have hrel : φ = (φ 0 / ψ 0) • ψ := by
        ext k; fin_cases k <;> dsimp
        · field_simp [h0]
        · field_simp [h0]; linear_combination heq
      rw [hrel, Matrix.mulVec_smul, hψ.2]
    · have hrel : φ = (φ 1 / ψ 1) • ψ := by
        ext k; fin_cases k <;> dsimp
        · field_simp [h1]; linear_combination -heq
        · field_simp [h1]
      rw [hrel, Matrix.mulVec_smul, hψ.2]
  have hcontra : φ = 0 := by
    ext k
    have hk := (congr_fun hmul k).symm.trans (congr_fun hφ_neg k)
    simp only [Pi.neg_apply] at hk
    exact CharZero.eq_neg_self_iff.mp hk
  rcases hφ_nz with h0 | h1
  · exact h0 (congr_fun hcontra 0)
  · exact h1 (congr_fun hcontra 1)

private def unnormPos (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then ((1 + v 2 : ℝ) : ℂ) else (v 0 : ℂ) + Complex.I * (v 1 : ℂ)

private def unnormNeg (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then (v 0 : ℂ) - Complex.I * (v 1 : ℂ) else ((1 - v 2 : ℝ) : ℂ)

private lemma pauliDot_unnormPos {v : Fin 3 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    (pauliDot v).mulVec (unnormPos v) = unnormPos v := by
  ext k
  simp only [unnormPos, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases k <;> dsimp <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

private lemma pauliDot_unnormNeg {v : Fin 3 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    (pauliDot v).mulVec (unnormNeg v) = unnormNeg v := by
  ext k
  simp only [unnormNeg, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases k <;> dsimp <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Canonical normalized $+1$-eigenvector of `pauliDot v` for unit `v ∈ S^2`. -/
noncomputable def canonicalSpinor (v : Fin 3 → ℝ) : Fin 2 → ℂ :=
  if 0 ≤ v 2 then
    ((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v
  else
    ((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v

lemma isPosSpinor_canonicalSpinor {v : Fin 3 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    IsPosSpinor v (canonicalSpinor v) := by
  have hv2_ge : -1 ≤ v 2 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2 + 1)]
  have hv2_le : v 2 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2 - 1)]
  by_cases h : 0 ≤ v 2
  · have hpos : 0 < 2 * (1 + v 2) := by linarith
    have hs_sq : Real.sqrt (2 * (1 + v 2)) ^ 2 = 2 * (1 + v 2) := Real.sq_sqrt hpos.le
    have hnorm0 : ‖(((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v) 0‖ ^ 2 =
        (1 + v 2) ^ 2 / (2 * (1 + v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormPos, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      ring
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hnorm1 : ‖(((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v) 1‖ ^ 2 =
        (v 0 ^ 2 + v 1 ^ 2) / (2 * (1 + v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormPos, h10, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      have hsq : ‖(v 0 : ℂ) + Complex.I * (v 1 : ℂ)‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        ring
      rw [hsq]; ring
    refine ⟨?_, ?_⟩
    · simp only [canonicalSpinor, h, ↓reduceIte]
      rw [hnorm0, hnorm1, ← add_div, div_eq_one_iff_eq hpos.ne']
      linarith
    · simp only [canonicalSpinor, h, ↓reduceIte, Matrix.mulVec_smul, pauliDot_unnormPos hv]
  · push Not at h
    have hpos : 0 < 2 * (1 - v 2) := by linarith
    have hs_sq : Real.sqrt (2 * (1 - v 2)) ^ 2 = 2 * (1 - v 2) := Real.sq_sqrt hpos.le
    have hnorm0 : ‖(((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v) 0‖ ^ 2 =
        (v 0 ^ 2 + v 1 ^ 2) / (2 * (1 - v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormNeg, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      have hsq : ‖(v 0 : ℂ) - Complex.I * (v 1 : ℂ)‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
        ring
      rw [hsq]; ring
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hnorm1 : ‖(((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v) 1‖ ^ 2 =
        (1 - v 2) ^ 2 / (2 * (1 - v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormNeg, h10, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      ring
    refine ⟨?_, ?_⟩
    · simp only [canonicalSpinor, not_le.mpr h, ↓reduceIte]
      rw [hnorm0, hnorm1, ← add_div, div_eq_one_iff_eq hpos.ne']
      linarith
    · simp only [canonicalSpinor, not_le.mpr h, ↓reduceIte, Matrix.mulVec_smul, pauliDot_unnormNeg hv]

/-- Canonical edge orientation $\Delta_\Gamma = \{(u, v) \in E : u < v\}$. -/
abbrev OriEdge (G : SimpleGraph (Fin n)) :=
  { e : Fin n × Fin n // G.Adj e.1 e.2 ∧ e.1 < e.2 }

/-- Source-preserving permutation group $P_G = \prod_{u} \operatorname{Sym}(N_G(u))$. -/
abbrev SourcePerm (G : SimpleGraph (Fin n)) :=
  ∀ u : Fin n, Equiv.Perm { w : Fin n // G.Adj u w }

/-- Numerator of Malkoun's Eq. (13) $G$-amplitude. -/
noncomputable def malkounNum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  ∑ σ : SourcePerm G, ∏ e : OriEdge G,
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)

/-- Denominator of Malkoun's Eq. (13) $G$-amplitude. -/
def malkounDen (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  ∏ e : OriEdge G, omega (ψ e.1.1 e.1.2) (ψ e.1.2 e.1.1)

/-- Malkoun's $G$-amplitude given any family of spinors $\psi_{ij}$. -/
noncomputable def malkounAmplitudeOfSpinors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  malkounNum G ψ / malkounDen G ψ

/-- Canonical Malkoun $G$-amplitude $\mathcal{A}_G(\mathbf{x})$ on $C_G(\mathbb{R}^3)$. -/
noncomputable def malkounAmplitude (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : ConfigSpace G) : ℂ :=
  malkounAmplitudeOfSpinors G (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v)))

/-! ### Phase / Scalar Invariance, Well-Definedness, and Planar Reality -/

private def oriSumEquiv (G : SimpleGraph (Fin n)) :
    OriEdge G ⊕ OriEdge G ≃ { p : Fin n × Fin n // G.Adj p.1 p.2 } where
  toFun
    | .inl e => ⟨(e.1.1, e.1.2), e.2.1⟩
    | .inr e => ⟨(e.1.2, e.1.1), e.2.1.symm⟩
  invFun p :=
    if h : p.1.1 < p.1.2 then .inl ⟨p.1, p.2, h⟩
    else .inr ⟨(p.1.2, p.1.1), p.2.symm, lt_of_le_of_ne (not_lt.mp h) (G.ne_of_adj p.2).symm⟩
  left_inv x := by
    cases x with
    | inl e => simp [e.2.2]
    | inr e => simp [not_lt.mpr e.2.2.le]
  right_inv p := by
    by_cases h : p.1.1 < p.1.2 <;> simp [h]

private def sigmaDirEquiv (G : SimpleGraph (Fin n)) :
    (Σ u : Fin n, { w : Fin n // G.Adj u w }) ≃ { p : Fin n × Fin n // G.Adj p.1 p.2 } where
  toFun uw := ⟨(uw.1, uw.2.1), uw.2.2⟩
  invFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  left_inv uw := by rcases uw with ⟨u, ⟨w, h⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨u, w⟩, h⟩; rfl

private lemma prod_ori_perm_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℂ) (σ : SourcePerm G) :
    (∏ e : OriEdge G,
      c e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1 * c e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
    ∏ e : OriEdge G, c e.1.1 e.1.2 * c e.1.2 e.1.1 := by
  let evalP (τ : SourcePerm G) (p : { p : Fin n × Fin n // G.Adj p.1 p.2 }) : ℂ :=
    c p.1.1 (τ p.1.1 ⟨p.1.2, p.2⟩).1
  have hfold (τ : SourcePerm G) :
      (∏ e : OriEdge G,
        c e.1.1 (τ e.1.1 ⟨e.1.2, e.2.1⟩).1 * c e.1.2 (τ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      ∏ uw : (Σ u : Fin n, { w : Fin n // G.Adj u w }), c uw.1 (τ uw.1 uw.2).1 := by
    rw [Finset.prod_mul_distrib]
    have hsum :
        (∏ e : OriEdge G, evalP τ ((oriSumEquiv G) (.inl e))) *
        (∏ e : OriEdge G, evalP τ ((oriSumEquiv G) (.inr e))) =
        ∏ p : { p : Fin n × Fin n // G.Adj p.1 p.2 }, evalP τ p := by
      calc (∏ e : OriEdge G, evalP τ ((oriSumEquiv G) (.inl e))) *
            (∏ e : OriEdge G, evalP τ ((oriSumEquiv G) (.inr e)))
          = ∏ x : OriEdge G ⊕ OriEdge G, evalP τ ((oriSumEquiv G) x) :=
              (Fintype.prod_sum_type (fun x => evalP τ ((oriSumEquiv G) x))).symm
        _ = ∏ p : { p : Fin n × Fin n // G.Adj p.1 p.2 }, evalP τ p :=
              Fintype.prod_equiv (oriSumEquiv G)
                (fun x => evalP τ ((oriSumEquiv G) x)) (evalP τ) (fun _ => rfl)
    have hsig :
        (∏ uw : (Σ u : Fin n, { w : Fin n // G.Adj u w }), c uw.1 (τ uw.1 uw.2).1) =
        ∏ p : { p : Fin n × Fin n // G.Adj p.1 p.2 }, evalP τ p :=
      Fintype.prod_equiv (sigmaDirEquiv G)
        (fun uw => c uw.1 (τ uw.1 uw.2).1) (evalP τ)
        (fun uw => by rcases uw with ⟨u, ⟨w, h⟩⟩; rfl)
    rw [hsig, ← hsum]
    rfl
  have hid : (∏ e : OriEdge G, c e.1.1 e.1.2 * c e.1.2 e.1.1) =
      ∏ uw : (Σ u : Fin n, { w : Fin n // G.Adj u w }), c uw.1 uw.2.1 := by
    simpa using hfold (fun _ => Equiv.refl _)
  rw [hfold σ, hid]
  exact Fintype.prod_equiv (Equiv.sigmaCongrRight σ)
    (fun uw => c uw.1 (σ uw.1 uw.2).1) (fun uw => c uw.1 uw.2.1)
    (fun uw => by rcases uw with ⟨u, w⟩; rfl)

/-- Scaling every spinor $\psi_{ij}$ by an arbitrary nonzero factor $c_{ij}$ leaves
`malkounAmplitudeOfSpinors` invariant. -/
theorem malkounAmplitude_scale_invariant (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℂ) (hc : ∀ u v, G.Adj u v → c u v ≠ 0)
    (ψ : Fin n → Fin n → Fin 2 → ℂ) :
    malkounAmplitudeOfSpinors G (fun u v k => c u v * ψ u v k) =
      malkounAmplitudeOfSpinors G ψ := by
  let C : ℂ := ∏ e : OriEdge G, c e.1.1 e.1.2 * c e.1.2 e.1.1
  have hC : C ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro e _
    exact mul_ne_zero (hc e.1.1 e.1.2 e.2.1) (hc e.1.2 e.1.1 e.2.1.symm)
  have hnum : malkounNum G (fun u v k => c u v * ψ u v k) = C * malkounNum G ψ := by
    simp only [malkounNum, omega_smul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib, prod_ori_perm_eq]
  have hden : malkounDen G (fun u v k => c u v * ψ u v k) = C * malkounDen G ψ := by
    simp only [malkounDen, omega_smul]
    rw [Finset.prod_mul_distrib]
  simp only [malkounAmplitudeOfSpinors, hnum, hden]
  exact mul_div_mul_left (malkounNum G ψ) (malkounDen G ψ) hC

/-- Any valid normalized $+1$-eigenvector family yields the exact same amplitude as `malkounAmplitude`. -/
theorem malkounAmplitude_eq_of_isPosSpinor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : ConfigSpace G) (ψ : Fin n → Fin n → Fin 2 → ℂ)
    (hψ : ∀ u v, G.Adj u v → IsPosSpinor (unitDir (x.1 u) (x.1 v)) (ψ u v)) :
    malkounAmplitudeOfSpinors G ψ = malkounAmplitude G x := by
  have hcanon : ∀ u v, G.Adj u v →
      IsPosSpinor (unitDir (x.1 u) (x.1 v)) (canonicalSpinor (unitDir (x.1 u) (x.1 v))) := by
    intro u v huv
    exact isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 u v huv))
  have hcol : ∀ u v, ∃ c : ℂ, c ≠ 0 ∧
      (G.Adj u v → ∀ k, ψ u v k = c * canonicalSpinor (unitDir (x.1 u) (x.1 v)) k) := by
    intro u v
    by_cases huv : G.Adj u v
    · rcases isPosSpinor_collinear (hcanon u v huv) (hψ u v huv) with ⟨c, hc, heq⟩
      exact ⟨c, hc, fun _ => heq⟩
    · exact ⟨1, one_ne_zero, fun h => False.elim (huv h)⟩
  choose c hc_ne hce using hcol
  have hψ_eq : ∀ σ : SourcePerm G,
      (∏ e : OriEdge G,
        omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)) =
      (∏ e : OriEdge G,
        omega
          (fun k => c e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1 *
            canonicalSpinor (unitDir (x.1 e.1.1) (x.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)) k)
          (fun k => c e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1 *
            canonicalSpinor (unitDir (x.1 e.1.2) (x.1 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)) k)) := by
    intro σ
    refine Finset.prod_congr rfl fun e _ => ?_
    have h1 : ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1 =
        fun k => c e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1 *
          canonicalSpinor (unitDir (x.1 e.1.1) (x.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)) k := by
      ext k; exact hce e.1.1 _ (σ e.1.1 ⟨e.1.2, e.2.1⟩).2 k
    have h2 : ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1 =
        fun k => c e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1 *
          canonicalSpinor (unitDir (x.1 e.1.2) (x.1 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)) k := by
      ext k; exact hce e.1.2 _ (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).2 k
    rw [h1, h2]
  have hden_eq : malkounDen G ψ =
      malkounDen G (fun u v k => c u v * canonicalSpinor (unitDir (x.1 u) (x.1 v)) k) := by
    refine Finset.prod_congr rfl fun e _ => ?_
    have h1 : ψ e.1.1 e.1.2 = fun k => c e.1.1 e.1.2 * canonicalSpinor (unitDir (x.1 e.1.1) (x.1 e.1.2)) k := by
      ext k; exact hce e.1.1 e.1.2 e.2.1 k
    have h2 : ψ e.1.2 e.1.1 = fun k => c e.1.2 e.1.1 * canonicalSpinor (unitDir (x.1 e.1.2) (x.1 e.1.1)) k := by
      ext k; exact hce e.1.2 e.1.1 e.2.1.symm k
    rw [h1, h2]
  have hnum_eq : malkounNum G ψ =
      malkounNum G (fun u v k => c u v * canonicalSpinor (unitDir (x.1 u) (x.1 v)) k) :=
    Finset.sum_congr rfl fun σ _ => hψ_eq σ
  calc malkounAmplitudeOfSpinors G ψ
      = malkounAmplitudeOfSpinors G (fun u v k => c u v * canonicalSpinor (unitDir (x.1 u) (x.1 v)) k) := by
          simp only [malkounAmplitudeOfSpinors, hnum_eq, hden_eq]
    _ = malkounAmplitude G x :=
          malkounAmplitude_scale_invariant G c (fun u v _ => hc_ne u v) _

/-- Any planar configuration (`∀ u, x u 2 = 0`) has purely real $G$-amplitude. -/
theorem planar_amplitude_im_eq_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : ConfigSpace G) (hz : ∀ u, x.1 u 2 = 0) :
    (malkounAmplitude G x).im = 0 := by
  let ψ := fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))
  let ψ' : Fin n → Fin n → Fin 2 → ℂ := fun u v k => starRingEnd ℂ (ψ u v (1 - k))
  have hψ : ∀ u v, G.Adj u v → IsPosSpinor (unitDir (x.1 u) (x.1 v)) (ψ u v) :=
    fun u v huv => isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 u v huv))
  have hψ' : ∀ u v, G.Adj u v → IsPosSpinor (unitDir (x.1 u) (x.1 v)) (ψ' u v) := by
    intro u v huv
    have hbase := hψ u v huv
    have hv2 : unitDir (x.1 u) (x.1 v) 2 = 0 := by
      simp [unitDir, hz u, hz v]
    refine ⟨?_, ?_⟩
    · have h01 : (1 - (0 : Fin 2)) = 1 := by decide
      have h11 : (1 - (1 : Fin 2)) = 0 := by decide
      simpa [ψ', h01, h11, Complex.norm_conj, add_comm] using hbase.1
    · have hm0 := congr_arg (starRingEnd ℂ) (congr_fun hbase.2 0)
      have hm1 := congr_arg (starRingEnd ℂ) (congr_fun hbase.2 1)
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, hv2, Complex.ofReal_zero,
        neg_zero, zero_mul, zero_add, add_zero, map_mul, map_add, map_sub, Complex.conj_ofReal,
        Complex.conj_I, neg_mul, sub_neg_eq_add] at hm0 hm1
      ext k
      have h01 : (1 - (0 : Fin 2)) = 1 := by decide
      have h11 : (1 - (1 : Fin 2)) = 0 := by decide
      fin_cases k <;> dsimp [ψ']
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, hv2, Complex.ofReal_zero,
          zero_mul, zero_add, h01, h11]
        simpa [sub_eq_add_neg, add_comm] using hm1
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, hv2, Complex.ofReal_zero,
          neg_zero, zero_mul, add_zero, h01, h11]
        simpa [sub_eq_add_neg] using hm0
  have homega_conj : ∀ a b : Fin 2 → ℂ,
      omega (fun k => starRingEnd ℂ (a (1 - k))) (fun k => starRingEnd ℂ (b (1 - k))) =
        -starRingEnd ℂ (omega a b) := by
    intro a b
    have h01 : (1 - (0 : Fin 2)) = 1 := by decide
    have h11 : (1 - (1 : Fin 2)) = 0 := by decide
    simp only [omega, h01, h11, map_sub, map_mul]
    ring
  have hnum_conj : malkounNum G ψ' =
      (-1 : ℂ) ^ (Finset.univ : Finset (OriEdge G)).card * starRingEnd ℂ (malkounNum G ψ) := by
    simp only [malkounNum, ψ']
    simp_rw [homega_conj, Finset.prod_neg, map_sum, map_prod, Finset.mul_sum]
  have hden_conj : malkounDen G ψ' =
      (-1 : ℂ) ^ (Finset.univ : Finset (OriEdge G)).card * starRingEnd ℂ (malkounDen G ψ) := by
    simp only [malkounDen, ψ']
    simp_rw [homega_conj, Finset.prod_neg, map_prod]
  have hamp_conj : malkounAmplitudeOfSpinors G ψ' = starRingEnd ℂ (malkounAmplitudeOfSpinors G ψ) := by
    simp only [malkounAmplitudeOfSpinors, hnum_conj, hden_conj, map_div₀]
    exact mul_div_mul_left _ _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  have heq : starRingEnd ℂ (malkounAmplitude G x) = malkounAmplitude G x := by
    calc starRingEnd ℂ (malkounAmplitude G x)
        = malkounAmplitudeOfSpinors G ψ' := hamp_conj.symm
      _ = malkounAmplitude G x := malkounAmplitude_eq_of_isPosSpinor G x ψ' hψ'
  exact Complex.conj_eq_iff_im.mp heq

/-- Unnormalized planar spinor along $p \to q$ in $z=0$:
$(r, \Delta x + i \Delta y)$ where $r = \|q - p\|$. -/
noncomputable def planarUnnormSpinor (p q : Fin 3 → ℝ) : Fin 2 → ℂ
  | 0 => (euclidNorm (fun j => q j - p j) : ℂ)
  | 1 => ((q 0 - p 0 : ℝ) : ℂ) + Complex.I * ((q 1 - p 1 : ℝ) : ℂ)

lemma malkounDen_planarUnnorm_ne_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : ConfigSpace G) (hz : ∀ u, x.1 u 2 = 0) :
    malkounDen G (fun u v => planarUnnormSpinor (x.1 u) (x.1 v)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro e _
  have hne : x.1 e.1.1 ≠ x.1 e.1.2 := x.2 e.1.1 e.1.2 e.2.1
  have hr_pos : 0 < euclidNorm (fun j => x.1 e.1.2 j - x.1 e.1.1 j) := euclidNorm_pos_of_ne hne
  have hsym : euclidNorm (fun j => x.1 e.1.1 j - x.1 e.1.2 j) =
      euclidNorm (fun j => x.1 e.1.2 j - x.1 e.1.1 j) := by
    simp only [euclidNorm]
    congr 1
    ring
  have hdx_dy : (x.1 e.1.2 0 - x.1 e.1.1 0) ^ 2 + (x.1 e.1.2 1 - x.1 e.1.1 1) ^ 2 > 0 := by
    have hsq := mul_self_pos.mpr hr_pos.ne'
    have hz1 := hz e.1.1
    have hz2 := hz e.1.2
    simp only [euclidNorm] at hsq
    rw [← sq, Real.sq_sqrt (by positivity)] at hsq
    nlinarith [sq_nonneg (x.1 e.1.2 2 - x.1 e.1.1 2)]
  have hdir_ne : ((x.1 e.1.2 0 - x.1 e.1.1 0 : ℝ) : ℂ) +
      Complex.I * ((x.1 e.1.2 1 - x.1 e.1.1 1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hre := congr_arg Complex.re h0
    have him := congr_arg Complex.im h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.zero_re,
      Complex.add_im, Complex.mul_im, one_mul, zero_add, Complex.zero_im] at hre him
    rw [hre, him] at hdx_dy
    norm_num at hdx_dy
  have homega :
      omega (planarUnnormSpinor (x.1 e.1.1) (x.1 e.1.2))
        (planarUnnormSpinor (x.1 e.1.2) (x.1 e.1.1)) =
      -2 * (euclidNorm (fun j => x.1 e.1.2 j - x.1 e.1.1 j) : ℂ) *
        (((x.1 e.1.2 0 - x.1 e.1.1 0 : ℝ) : ℂ) +
          Complex.I * ((x.1 e.1.2 1 - x.1 e.1.1 1 : ℝ) : ℂ)) := by
    simp only [omega, planarUnnormSpinor, hsym, Complex.ofReal_sub]
    ring
  rw [homega]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hr_pos.ne')) hdir_ne

theorem malkounAmplitude_eq_planarUnnorm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : ConfigSpace G) (hz : ∀ u, x.1 u 2 = 0) :
    malkounAmplitude G x =
      malkounAmplitudeOfSpinors G (fun u v => planarUnnormSpinor (x.1 u) (x.1 v)) := by
  let c : Fin n → Fin n → ℂ :=
    fun u v => ((euclidNorm (fun j => x.1 v j - x.1 u j) * Real.sqrt 2 : ℝ) : ℂ)
  have hc : ∀ u v, G.Adj u v → c u v ≠ 0 := by
    intro u v huv
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (euclidNorm_pos_of_ne (x.2 u v huv)).ne'
      (Real.sqrt_ne_zero'.mpr (by norm_num)))
  have hmatch : ∀ u v, G.Adj u v → ∀ k,
      planarUnnormSpinor (x.1 u) (x.1 v) k = c u v * canonicalSpinor (unitDir (x.1 u) (x.1 v)) k := by
    intro u v huv k
    have hr : euclidNorm (fun j => x.1 v j - x.1 u j) ≠ 0 :=
      (euclidNorm_pos_of_ne (x.2 u v huv)).ne'
    have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hv2 : unitDir (x.1 u) (x.1 v) 2 = 0 := by simp [unitDir, hz u, hz v]
    have hc_mul : ((euclidNorm (fun j => x.1 v j - x.1 u j) * Real.sqrt 2 : ℝ) : ℂ) *
        ((1 / Real.sqrt 2 : ℝ) : ℂ) = (euclidNorm (fun j => x.1 v j - x.1 u j) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [hs2]
    fin_cases k
    · simp only [planarUnnormSpinor, canonicalSpinor, hv2, le_refl, ↓reduceIte,
        Pi.smul_apply, smul_eq_mul, unnormPos, add_zero, mul_one,
        Complex.ofReal_one]
      have h0eq : ((⟨0, by omega⟩ : Fin 2) = 0) := rfl
      simp only [h0eq, ↓reduceIte, mul_one]
      dsimp only [c]
      exact hc_mul.symm
    · simp only [planarUnnormSpinor, canonicalSpinor, hv2, le_refl, ↓reduceIte,
        Pi.smul_apply, smul_eq_mul, unnormPos]
      have h1ne : ((⟨1, by omega⟩ : Fin 2) ≠ 0) := by decide
      simp only [h1ne, ↓reduceIte]
      change ((x.1 v 0 - x.1 u 0 : ℝ) : ℂ) + Complex.I * ((x.1 v 1 - x.1 u 1 : ℝ) : ℂ) =
        c u v * (((1 / Real.sqrt (2 * (1 + 0)) : ℝ) : ℂ) *
          ((unitDir (x.1 u) (x.1 v) 0 : ℂ) + Complex.I * (unitDir (x.1 u) (x.1 v) 1 : ℂ)))
      have h20 : (2 * (1 + (0 : ℝ))) = 2 := by ring
      rw [h20, ← mul_assoc, hc_mul]
      simp only [unitDir, Complex.ofReal_div]
      have hrc : (euclidNorm (fun j => x.1 v j - x.1 u j) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
      field_simp [hrc]
  have hnum : malkounNum G (fun u v => planarUnnormSpinor (x.1 u) (x.1 v)) =
      malkounNum G (fun u v k => c u v * canonicalSpinor (unitDir (x.1 u) (x.1 v)) k) := by
    refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => ?_
    dsimp only
    have h1 : planarUnnormSpinor (x.1 e.1.1) (x.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) =
        fun k => c e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1 *
          canonicalSpinor (unitDir (x.1 e.1.1) (x.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)) k := by
      ext k; exact hmatch e.1.1 _ (σ e.1.1 ⟨e.1.2, e.2.1⟩).2 k
    have h2 : planarUnnormSpinor (x.1 e.1.2) (x.1 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
        fun k => c e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1 *
          canonicalSpinor (unitDir (x.1 e.1.2) (x.1 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)) k := by
      ext k; exact hmatch e.1.2 _ (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).2 k
    rw [h1, h2]
  have hden : malkounDen G (fun u v => planarUnnormSpinor (x.1 u) (x.1 v)) =
      malkounDen G (fun u v k => c u v * canonicalSpinor (unitDir (x.1 u) (x.1 v)) k) := by
    refine Finset.prod_congr rfl fun e _ => ?_
    dsimp only
    have h1 : planarUnnormSpinor (x.1 e.1.1) (x.1 e.1.2) =
        fun k => c e.1.1 e.1.2 * canonicalSpinor (unitDir (x.1 e.1.1) (x.1 e.1.2)) k := by
      ext k; exact hmatch e.1.1 e.1.2 e.2.1 k
    have h2 : planarUnnormSpinor (x.1 e.1.2) (x.1 e.1.1) =
        fun k => c e.1.2 e.1.1 * canonicalSpinor (unitDir (x.1 e.1.2) (x.1 e.1.1)) k := by
      ext k; exact hmatch e.1.2 e.1.1 e.2.1.symm k
    rw [h1, h2]
  rw [malkounAmplitude, ← malkounAmplitude_scale_invariant G c hc (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v)))]
  simp only [malkounAmplitudeOfSpinors, hnum, hden]

end GeneralDefinitions

/-! ## Part 3: Combinatorics, Dicke Tensor Identities, and Computable Gaussian-Integer Evaluator -/

section PermDickeAndGI

/-- Coefficient of $X^{n-k} Y^k$ in $\prod_{i=0}^{n-1} (M_{i,0} X + M_{i,1} Y)$. -/
def dickePolyCoeff {R : Type*} [Semiring R] : ∀ {n : ℕ}, (Fin n → Fin 2 → R) → ℕ → R
  | 0, _, k => if k = 0 then 1 else 0
  | _ + 1, M, 0 => M 0 0 * dickePolyCoeff (fun j => M j.succ) 0
  | _ + 1, M, k + 1 =>
      M 0 0 * dickePolyCoeff (fun j => M j.succ) (k + 1) +
      M 0 1 * dickePolyCoeff (fun j => M j.succ) k

lemma dickePolyCoeff_eq_zero_of_lt {R : Type*} [Semiring R] :
    ∀ {n : ℕ} (M : Fin n → Fin 2 → R) {k : ℕ}, n < k → dickePolyCoeff M k = 0
  | 0, _, k, hk => by
      have hk0 : k ≠ 0 := by omega
      simp [dickePolyCoeff, hk0]
  | n + 1, M, k, hk => by
      cases k with
      | zero => omega
      | succ k' =>
          have h1 : n < k' + 1 := by omega
          have h2 : n < k' := by omega
          simp [dickePolyCoeff, dickePolyCoeff_eq_zero_of_lt _ h1,
            dickePolyCoeff_eq_zero_of_lt _ h2]

/-- Hamming weight (number of $1$-bits) of a bit vector `Fin n → Fin 2`. -/
def bitSum {n : ℕ} (c : Fin n → Fin 2) : ℕ :=
  ∑ i : Fin n, (c i).val

lemma bitSum_le {n : ℕ} (c : Fin n → Fin 2) : bitSum c ≤ n := by
  calc bitSum c = ∑ i : Fin n, (c i).val := rfl
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (Fin.is_lt (c i))
    _ = n := by simp

private lemma fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

private lemma card_filter_bit_one {m : ℕ} (c : Fin m → Fin 2) :
    (Finset.univ.filter fun i : Fin m => c i = 1).card = bitSum c := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases fin2_cases (c i) with h | h <;> simp [h]

private lemma card_filter_bit_zero {m : ℕ} (c : Fin m → Fin 2) :
    (Finset.univ.filter fun i : Fin m => c i = 0).card = m - bitSum c := by
  have hpart : (Finset.univ.filter fun i : Fin m => c i = 0).card +
      (Finset.univ.filter fun i : Fin m => c i = 1).card = m := by
    rw [← Finset.card_union_of_disjoint]
    · convert Finset.card_fin m
      ext i
      rcases fin2_cases (c i) with h | h <;> simp [h]
    · rw [Finset.disjoint_filter]
      intro i _ h0 h1
      rw [h0] at h1
      exact Fin.zero_ne_one h1
  rw [card_filter_bit_one] at hpart
  omega

/-- Key combinatorial theorem reducing vertex-permutation sums over arbitrary degree `n`
and bit pattern `c : Fin n → Fin 2` to `dickePolyCoeff`. -/
theorem perm_col_sum_eq_dicke {R : Type*} [CommRing R] :
    ∀ (n : ℕ) (M : Fin n → Fin 2 → R) (c : Fin n → Fin 2),
      (∑ τ : Equiv.Perm (Fin n), ∏ i : Fin n, M i (c (τ i))) =
        (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
          dickePolyCoeff M (bitSum c)
  | 0, M, c => by
      have hsub : Subsingleton (Equiv.Perm (Fin 0)) := inferInstance
      have hc0 : bitSum c = 0 := by simp [bitSum]
      simp [hc0, dickePolyCoeff]
  | n + 1, M, c => by
      let M' : Fin n → Fin 2 → R := fun j => M j.succ
      have hdecomp :
          (∑ τ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin (n + 1), M i (c (τ i))) =
          ∑ p : Fin (n + 1), M 0 (c p) *
            ∑ e : Equiv.Perm (Fin n), ∏ j : Fin n, M' j (c ((Equiv.swap 0 p) (e j).succ)) := by
        rw [← Fintype.sum_equiv Equiv.Perm.decomposeFin.symm
          (fun pe : Fin (n + 1) × Equiv.Perm (Fin n) =>
            ∏ i : Fin (n + 1), M i (c ((Equiv.Perm.decomposeFin.symm pe) i)))
          (fun τ => ∏ i : Fin (n + 1), M i (c (τ i))) (fun _ => rfl)]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Equiv.Perm.decomposeFin_symm_apply_succ]
      have hbit : ∀ p : Fin (n + 1),
          (c p).val + bitSum (fun j : Fin n => c ((Equiv.swap 0 p) j.succ)) = bitSum c := by
        intro p
        have hperm := Equiv.sum_comp (Equiv.swap (0 : Fin (n + 1)) p) (fun y => (c y).val)
        rw [Fin.sum_univ_succ] at hperm
        simpa [Equiv.swap_apply_left, bitSum] using hperm
      have hinner : ∀ p : Fin (n + 1),
          (M 0 (c p) * ∑ e : Equiv.Perm (Fin n),
            ∏ j : Fin n, M' j (c ((Equiv.swap 0 p) (e j).succ))) =
          if c p = 0 then
            M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
              dickePolyCoeff M' (bitSum c)
          else
            M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
              dickePolyCoeff M' (bitSum c - 1) := by
        intro p
        have ih := perm_col_sum_eq_dicke n M' (fun j => c ((Equiv.swap 0 p) j.succ))
        rw [ih]
        have hp := hbit p
        rcases fin2_cases (c p) with hcp | hcp
        · have hzero : (0 : Fin 2).val = 0 := rfl
          have hbs : bitSum (fun j : Fin n => c ((Equiv.swap 0 p) j.succ)) = bitSum c := by
            rw [hcp, hzero, zero_add] at hp; exact hp
          simp only [hcp, ↓reduceIte, hbs, mul_assoc]
        · have hone : (1 : Fin 2).val = 1 := rfl
          have hbs : bitSum (fun j : Fin n => c ((Equiv.swap 0 p) j.succ)) = bitSum c - 1 := by
            rw [hcp, hone] at hp; omega
          have h10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [hcp, h10, ↓reduceIte, hbs, ← mul_assoc]
      rw [hdecomp]
      simp_rw [hinner]
      have hsplit :
          (∑ p : Fin (n + 1),
            if c p = 0 then
              M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
                dickePolyCoeff M' (bitSum c)
            else
              M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
                dickePolyCoeff M' (bitSum c - 1)) =
          ((n + 1 - bitSum c : ℕ) : R) *
            (M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
              dickePolyCoeff M' (bitSum c)) +
          ((bitSum c : ℕ) : R) *
            (M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
              dickePolyCoeff M' (bitSum c - 1)) := by
        have hunion : (Finset.univ : Finset (Fin (n + 1))) =
            Finset.univ.filter (fun p => c p = 0) ∪ Finset.univ.filter (fun p => c p = 1) := by
          ext p; rcases fin2_cases (c p) with h | h <;> simp [h]
        have hdisj : Disjoint (Finset.univ.filter fun p : Fin (n + 1) => c p = 0)
            (Finset.univ.filter fun p : Fin (n + 1) => c p = 1) := by
          rw [Finset.disjoint_filter]
          intro p _ h0 h1; rw [h0] at h1; exact Fin.zero_ne_one h1
        conv_lhs => rw [hunion, Finset.sum_union hdisj]
        have s0_eq :
            (∑ p ∈ Finset.univ.filter fun p : Fin (n + 1) => c p = 0,
              if c p = 0 then
                M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
                  dickePolyCoeff M' (bitSum c)
              else
                M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
                  dickePolyCoeff M' (bitSum c - 1)) =
            ∑ _p ∈ Finset.univ.filter fun p : Fin (n + 1) => c p = 0,
              (M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
                dickePolyCoeff M' (bitSum c)) :=
          Finset.sum_congr rfl fun p hp => by
            simp only [Finset.mem_filter] at hp
            simp [hp.2]
        have s0 :
            (∑ p ∈ Finset.univ.filter fun p : Fin (n + 1) => c p = 0,
              if c p = 0 then
                M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
                  dickePolyCoeff M' (bitSum c)
              else
                M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
                  dickePolyCoeff M' (bitSum c - 1)) =
            ((n + 1 - bitSum c : ℕ) : R) *
              (M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
                dickePolyCoeff M' (bitSum c)) := by
          rw [s0_eq, Finset.sum_const, card_filter_bit_zero, nsmul_eq_mul]
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        have s1_eq :
            (∑ p ∈ Finset.univ.filter fun p : Fin (n + 1) => c p = 1,
              if c p = 0 then
                M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
                  dickePolyCoeff M' (bitSum c)
              else
                M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
                  dickePolyCoeff M' (bitSum c - 1)) =
            ∑ _p ∈ Finset.univ.filter fun p : Fin (n + 1) => c p = 1,
              (M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
                dickePolyCoeff M' (bitSum c - 1)) :=
          Finset.sum_congr rfl fun p hp => by
            simp only [Finset.mem_filter] at hp
            simp [hp.2, h10]
        have s1 :
            (∑ p ∈ Finset.univ.filter fun p : Fin (n + 1) => c p = 1,
              if c p = 0 then
                M 0 0 * (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
                  dickePolyCoeff M' (bitSum c)
              else
                M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
                  dickePolyCoeff M' (bitSum c - 1)) =
            ((bitSum c : ℕ) : R) *
              (M 0 1 * ((((bitSum c - 1).factorial * (n - (bitSum c - 1)).factorial : ℕ) : R)) *
                dickePolyCoeff M' (bitSum c - 1)) := by
          rw [s1_eq, Finset.sum_const, card_filter_bit_one, nsmul_eq_mul]
        rw [s0, s1]
      rw [hsplit]
      have hbd : bitSum c ≤ n + 1 := bitSum_le c
      rcases hk : bitSum c with _ | k
      · simp [dickePolyCoeff, Nat.factorial_succ]
        ring
      · have hkn : k ≤ n := by omega
        have hfact_k : (k + 1) * k.factorial = (k + 1).factorial :=
          by rw [Nat.factorial_succ]
        have hsub1 : n - k = n + 1 - (k + 1) := by omega
        rcases eq_or_lt_of_le hkn with rfl | hk_lt
        · have hdz : dickePolyCoeff (fun j => M j.succ) (k + 1) = 0 :=
            dickePolyCoeff_eq_zero_of_lt _ (by omega)
          rw [← hsub1]
          simp only [dickePolyCoeff, hdz, Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero,
            zero_mul, Nat.factorial_zero, mul_one, mul_zero, zero_add]
          have hcast_k : ((k + 1 : ℕ) : R) * ((k.factorial : ℕ) : R) =
              (((k + 1).factorial : ℕ) : R) := by
            simpa [Nat.cast_mul] using congrArg (Nat.cast : ℕ → R) hfact_k
          calc ((k + 1 : ℕ) : R) * (M 0 1 * ((k.factorial : ℕ) : R) * dickePolyCoeff M' k)
              = M 0 1 * dickePolyCoeff M' k *
                  (((k + 1 : ℕ) : R) * ((k.factorial : ℕ) : R)) := by ring
            _ = (((k + 1).factorial : ℕ) : R) * (M 0 1 * dickePolyCoeff M' k) := by
                  rw [hcast_k]; ring
        · have hm : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
          have hfact_m : (n + 1 - (k + 1)) * (n - (k + 1)).factorial =
              (n + 1 - (k + 1)).factorial := by
            conv_lhs => rw [hm, ← Nat.factorial_succ, ← hm]
          have hnat1_N : (n + 1 - (k + 1)) * ((k + 1).factorial * (n - (k + 1)).factorial) =
              (k + 1).factorial * (n + 1 - (k + 1)).factorial := by
            calc (n + 1 - (k + 1)) * ((k + 1).factorial * (n - (k + 1)).factorial)
                = (k + 1).factorial * ((n + 1 - (k + 1)) * (n - (k + 1)).factorial) := by ring
              _ = (k + 1).factorial * (n + 1 - (k + 1)).factorial := by rw [hfact_m]
          have hnat1 : ((n + 1 - (k + 1) : ℕ) : R) *
              (((k + 1).factorial * (n - (k + 1)).factorial : ℕ) : R) =
              (((k + 1).factorial * (n + 1 - (k + 1)).factorial : ℕ) : R) := by
            simpa [Nat.cast_mul] using congrArg (Nat.cast : ℕ → R) hnat1_N
          have hnat2_N : (k + 1) * (k.factorial * (n - k).factorial) =
              (k + 1).factorial * (n + 1 - (k + 1)).factorial := by
            rw [← hsub1]
            calc (k + 1) * (k.factorial * (n - k).factorial)
                = ((k + 1) * k.factorial) * (n - k).factorial := by ring
              _ = (k + 1).factorial * (n - k).factorial := by rw [hfact_k]
          have hnat2 : ((k + 1 : ℕ) : R) * ((k.factorial * (n - k).factorial : ℕ) : R) =
              (((k + 1).factorial * (n + 1 - (k + 1)).factorial : ℕ) : R) := by
            simpa [Nat.cast_mul] using congrArg (Nat.cast : ℕ → R) hnat2_N
          simp only [dickePolyCoeff, Nat.add_sub_cancel]
          calc ((n + 1 - (k + 1) : ℕ) : R) *
                  (M 0 0 * (((k + 1).factorial * (n - (k + 1)).factorial : ℕ) : R) *
                    dickePolyCoeff M' (k + 1)) +
                ((k + 1 : ℕ) : R) *
                  (M 0 1 * ((k.factorial * (n - k).factorial : ℕ) : R) *
                    dickePolyCoeff M' k)
              = M 0 0 * dickePolyCoeff M' (k + 1) *
                  (((n + 1 - (k + 1) : ℕ) : R) *
                    (((k + 1).factorial * (n - (k + 1)).factorial : ℕ) : R)) +
                M 0 1 * dickePolyCoeff M' k *
                  (((k + 1 : ℕ) : R) * ((k.factorial * (n - k).factorial : ℕ) : R)) := by ring
            _ = M 0 0 * dickePolyCoeff M' (k + 1) *
                  (((k + 1).factorial * (n + 1 - (k + 1)).factorial : ℕ) : R) +
                M 0 1 * dickePolyCoeff M' k *
                  (((k + 1).factorial * (n + 1 - (k + 1)).factorial : ℕ) : R) := by
                  rw [hnat1, hnat2]
            _ = (((k + 1).factorial * (n + 1 - (k + 1)).factorial : ℕ) : R) *
                  (M 0 0 * dickePolyCoeff M' (k + 1) + M 0 1 * dickePolyCoeff M' k) := by ring

/-- Permutation sum on the left index `σ r` (matching `malkounNum`), proved by inverting `σ`. -/
theorem perm_sigma_sum_eq_dicke {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin n → Fin 2 → R) (c : Fin n → Fin 2) :
    (∑ σ : Equiv.Perm (Fin n), ∏ r : Fin n, M (σ r) (c r)) =
      (((bitSum c).factorial * (n - bitSum c).factorial : ℕ) : R) *
        dickePolyCoeff M (bitSum c) := by
  have heq : (∑ σ : Equiv.Perm (Fin n), ∏ r : Fin n, M (σ r) (c r)) =
      ∑ τ : Equiv.Perm (Fin n), ∏ i : Fin n, M i (c (τ i)) := by
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    exact Fintype.prod_equiv σ (fun r => M (σ r) (c r)) (fun i => M i (c (σ⁻¹ i)))
      (fun r => by simp)
  rw [heq, perm_col_sum_eq_dicke]

/-- Recursive binary sum over `Fin m → Fin 2` (fast and `Fintype`-free for kernel `decide`). -/
def sumBits {R : Type*} [Add R] : ∀ m : ℕ, ((Fin m → Fin 2) → R) → R
  | 0, g => g Fin.elim0
  | m + 1, g => sumBits m (fun f => g (Fin.cons 0 f)) + sumBits m (fun f => g (Fin.cons 1 f))

private def finConsEquiv (m : ℕ) (α : Type*) : (α × (Fin m → α)) ≃ (Fin (m + 1) → α) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv p := Prod.ext rfl (funext fun i => by simp)
  right_inv f := funext fun i => by
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl

lemma sum_bitFun_eq_sumBits {R : Type*} [AddCommMonoid R] :
    ∀ (m : ℕ) (g : (Fin m → Fin 2) → R), (∑ b : Fin m → Fin 2, g b) = sumBits m g
  | 0, g => by
      have hsub : Subsingleton (Fin 0 → Fin 2) := ⟨fun a b => funext fun x => Fin.elim0 x⟩
      have hu : ∀ f : Fin 0 → Fin 2, f = Fin.elim0 := fun f => Subsingleton.elim f Fin.elim0
      simp [sumBits, hu]
  | m + 1, g => by
      rw [← Fintype.sum_equiv (finConsEquiv m (Fin 2))
        (fun p => g (Fin.cons p.1 p.2)) g (fun _ => rfl)]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [sumBits, ← sum_bitFun_eq_sumBits m]

lemma prod_fin2_sub_eq_sumBits {R : Type*} [CommRing R] (m : ℕ) (f : Fin m → Fin 2 → R) :
    (∏ i : Fin m, (f i 0 - f i 1)) =
      ∑ b : Fin m → Fin 2, (∏ i : Fin m, (if b i = 0 then (1 : R) else -1) * f i (b i)) := by
  have hrow : ∀ i : Fin m, f i 0 - f i 1 =
      ∑ j : Fin 2, (if j = 0 then (1 : R) else -1) * f i j := fun i => by
    rw [Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  simp_rw [hrow]
  exact Fintype.prod_sum (fun i j => (if j = 0 then (1 : R) else -1) * f i j)

/-- Exact Gaussian integer $\mathbb{Z}[i]$ represented as `(re, im)` pairs for kernel `decide`. -/
structure GI where
  re : ℤ
  im : ℤ
  deriving DecidableEq

namespace GI

def zero : GI := ⟨0, 0⟩
def one : GI := ⟨1, 0⟩
def ofInt (z : ℤ) : GI := ⟨z, 0⟩
def add (a b : GI) : GI := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : GI) : GI := ⟨a.re - b.re, a.im - b.im⟩
def neg (a : GI) : GI := ⟨-a.re, -a.im⟩
def mul (a b : GI) : GI := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

instance : Zero GI := ⟨GI.zero⟩
instance : One GI := ⟨GI.one⟩
instance : Add GI := ⟨GI.add⟩
instance : Sub GI := ⟨GI.sub⟩
instance : Neg GI := ⟨GI.neg⟩
instance : Mul GI := ⟨GI.mul⟩

/-- Ring embedding `GI → ℂ`. -/
noncomputable def toC (z : GI) : ℂ := (z.re : ℂ) + Complex.I * (z.im : ℂ)

@[simp] lemma toC_zero : toC (0 : GI) = 0 := by
  change ((0 : ℤ) : ℂ) + Complex.I * ((0 : ℤ) : ℂ) = 0
  simp
@[simp] lemma toC_one : toC (1 : GI) = 1 := by
  change ((1 : ℤ) : ℂ) + Complex.I * ((0 : ℤ) : ℂ) = 1
  simp
@[simp] lemma toC_ofInt (n : ℤ) : toC (ofInt n) = (n : ℂ) := by simp [toC, ofInt]
@[simp] lemma toC_add (a b : GI) : toC (a + b) = toC a + toC b := by
  change toC (GI.add a b) = toC a + toC b
  simp only [toC, GI.add, Int.cast_add]
  ring
@[simp] lemma toC_sub (a b : GI) : toC (a - b) = toC a - toC b := by
  change toC (GI.sub a b) = toC a - toC b
  simp only [toC, GI.sub, Int.cast_sub]
  ring
@[simp] lemma toC_neg (a : GI) : toC (-a) = -toC a := by
  change toC (GI.neg a) = -toC a
  simp only [toC, GI.neg, Int.cast_neg]
  ring
@[simp] lemma toC_mul (a b : GI) : toC (a * b) = toC a * toC b := by
  change toC (GI.mul a b) = toC a * toC b
  simp only [toC, GI.mul, Int.cast_sub, Int.cast_add, Int.cast_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

def dickePolyCoeffGI : ∀ {n : ℕ}, (Fin n → Fin 2 → GI) → ℕ → GI
  | 0, _, k => if k = 0 then 1 else 0
  | _ + 1, M, 0 => M 0 0 * dickePolyCoeffGI (fun j => M j.succ) 0
  | _ + 1, M, k + 1 =>
      M 0 0 * dickePolyCoeffGI (fun j => M j.succ) (k + 1) +
      M 0 1 * dickePolyCoeffGI (fun j => M j.succ) k

lemma toC_dickePolyCoeffGI : ∀ {n : ℕ} (M : Fin n → Fin 2 → GI) (k : ℕ),
    toC (dickePolyCoeffGI M k) = dickePolyCoeff (fun i b => toC (M i b)) k
  | 0, M, k => by by_cases hk : k = 0 <;> simp [dickePolyCoeffGI, dickePolyCoeff, hk]
  | n + 1, M, 0 => by
      simp [dickePolyCoeffGI, dickePolyCoeff, toC_dickePolyCoeffGI (fun j => M j.succ) 0]
  | n + 1, M, k + 1 => by
      simp [dickePolyCoeffGI, dickePolyCoeff,
        toC_dickePolyCoeffGI (fun j => M j.succ) (k + 1),
        toC_dickePolyCoeffGI (fun j => M j.succ) k]

lemma toC_sumBits : ∀ (m : ℕ) (g : (Fin m → Fin 2) → GI),
    toC (sumBits m g) = sumBits m (fun f => toC (g f))
  | 0, g => rfl
  | m + 1, g => by
      simp only [sumBits, toC_add, toC_sumBits m]

end GI

end PermDickeAndGI

/-! ### Graph Definition, Connectedness, and Bridge + Dicke Factorization for `barbellK4Graph` -/

section BarbellCombinatorics

/-- Computable adjacency predicate for the 8-vertex, 13-edge barbell graph ($K_4$--bridge--$K_4$). -/
def barbellAdjBool (u v : Fin 8) : Bool :=
  (u != v) &&
    ((u.val < 4 && v.val < 4) ||
     (3 < u.val && 3 < v.val) ||
     (u.val == 3 && v.val == 4) ||
     (u.val == 4 && v.val == 3))

/-- The 8-vertex, 13-edge barbell graph: cliques $\{0,1,2,3\}$ and $\{4,5,6,7\}$ joined by bridge $\{3,4\}$. -/
def barbellK4Graph : SimpleGraph (Fin 8) where
  Adj u v := barbellAdjBool u v = true
  symm := by
    have h : ∀ u v : Fin 8, barbellAdjBool u v = true → barbellAdjBool v u = true := by decide
    exact ⟨h⟩
  loopless := by
    have h : ∀ u : Fin 8, barbellAdjBool u u ≠ true := by decide
    exact ⟨h⟩

instance : DecidableRel barbellK4Graph.Adj := fun u v =>
  inferInstanceAs (Decidable (barbellAdjBool u v = true))

theorem barbellK4Graph_connected : barbellK4Graph.Connected := by
  refine ⟨fun u v => ?_⟩
  have h34 : barbellK4Graph.Adj 3 4 := by decide
  have hreach3 : ∀ w : Fin 8, barbellK4Graph.Reachable 3 w := by
    intro w
    fin_cases w
    · exact (by decide : barbellK4Graph.Adj 3 0).reachable
    · exact (by decide : barbellK4Graph.Adj 3 1).reachable
    · exact (by decide : barbellK4Graph.Adj 3 2).reachable
    · exact SimpleGraph.Reachable.refl 3
    · exact h34.reachable
    · exact h34.reachable.trans (by decide : barbellK4Graph.Adj 4 5).reachable
    · exact h34.reachable.trans (by decide : barbellK4Graph.Adj 4 6).reachable
    · exact h34.reachable.trans (by decide : barbellK4Graph.Adj 4 7).reachable
  exact (hreach3 u).symm.trans (hreach3 v)

/-- Vertex degrees of `barbellK4Graph`. -/
@[reducible] def barbellDeg : Fin 8 → ℕ
  | 0 => 3 | 1 => 3 | 2 => 3 | 3 => 4
  | 4 => 4 | 5 => 3 | 6 => 3 | 7 => 3

/-- Canonical neighbor enumeration at each vertex of `barbellK4Graph`. -/
def barbellNbr : ∀ u : Fin 8, Fin (barbellDeg u) → Fin 8
  | 0 => fun j => match j with | 0 => 1 | 1 => 2 | 2 => 3
  | 1 => fun j => match j with | 0 => 0 | 1 => 2 | 2 => 3
  | 2 => fun j => match j with | 0 => 0 | 1 => 1 | 2 => 3
  | 3 => fun j => match j with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4
  | 4 => fun j => match j with | 0 => 3 | 1 => 5 | 2 => 6 | 3 => 7
  | 5 => fun j => match j with | 0 => 4 | 1 => 6 | 2 => 7
  | 6 => fun j => match j with | 0 => 4 | 1 => 5 | 2 => 7
  | 7 => fun j => match j with | 0 => 4 | 1 => 5 | 2 => 6

/-- Inverse neighbor-slot lookup at each vertex of `barbellK4Graph`. -/
def barbellNbrIdx : ∀ u : Fin 8, Fin 8 → Fin (barbellDeg u)
  | 0 => fun w => if w.val == 1 then 0 else if w.val == 2 then 1 else if w.val == 3 then 2 else 0
  | 1 => fun w => if w.val == 0 then 0 else if w.val == 2 then 1 else if w.val == 3 then 2 else 0
  | 2 => fun w => if w.val == 0 then 0 else if w.val == 1 then 1 else if w.val == 3 then 2 else 0
  | 3 => fun w => if w.val == 0 then 0 else if w.val == 1 then 1 else if w.val == 2 then 2 else if w.val == 4 then 3 else 0
  | 4 => fun w => if w.val == 3 then 0 else if w.val == 5 then 1 else if w.val == 6 then 2 else if w.val == 7 then 3 else 0
  | 5 => fun w => if w.val == 4 then 0 else if w.val == 6 then 1 else if w.val == 7 then 2 else 0
  | 6 => fun w => if w.val == 4 then 0 else if w.val == 5 then 1 else if w.val == 7 then 2 else 0
  | 7 => fun w => if w.val == 4 then 0 else if w.val == 5 then 1 else if w.val == 6 then 2 else 0

private lemma barbellNbr_adj : ∀ u : Fin 8, ∀ j : Fin (barbellDeg u),
    barbellK4Graph.Adj u (barbellNbr u j) := by
  intro u; fin_cases u <;> decide

private lemma barbellNbr_left_inv : ∀ u : Fin 8, ∀ j : Fin (barbellDeg u),
    barbellNbrIdx u (barbellNbr u j) = j := by
  intro u; fin_cases u <;> decide

private lemma barbellNbr_right_inv : ∀ u w : Fin 8,
    barbellK4Graph.Adj u w → barbellNbr u (barbellNbrIdx u w) = w := by
  intro u; fin_cases u <;> decide

private def barbellNbrEquiv (u : Fin 8) :
    Fin (barbellDeg u) ≃ { w : Fin 8 // barbellK4Graph.Adj u w } where
  toFun j := ⟨barbellNbr u j, barbellNbr_adj u j⟩
  invFun w := barbellNbrIdx u w.1
  left_inv j := barbellNbr_left_inv u j
  right_inv w := Subtype.ext (barbellNbr_right_inv u w.1 w.2)

abbrev LeftPerm := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 4)
abbrev RightPerm := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

private def matchFin8 {P : Fin 8 → Type*}
    (x0 : P 0) (x1 : P 1) (x2 : P 2) (x3 : P 3)
    (x4 : P 4) (x5 : P 5) (x6 : P 6) (x7 : P 7) : ∀ u : Fin 8, P u
  | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3
  | 4 => x4 | 5 => x5 | 6 => x6 | 7 => x7

private def leftRightPiEquiv :
    LeftPerm × RightPerm ≃ (∀ u : Fin 8, Equiv.Perm (Fin (barbellDeg u))) where
  toFun p := matchFin8 p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  invFun f := ((f 0, f 1, f 2, f 3), (f 4, f 5, f 6, f 7))
  left_inv _ := rfl
  right_inv f := funext fun u => by fin_cases u <;> rfl

private def barbellSourcePermEquiv : LeftPerm × RightPerm ≃ SourcePerm barbellK4Graph :=
  leftRightPiEquiv.trans (Equiv.piCongrRight fun u => Equiv.permCongr (barbellNbrEquiv u))

def leftEdgePairs : Fin 6 → Fin 8 × Fin 8 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def rightEdgePairs : Fin 6 → Fin 8 × Fin 8 :=
  ![(4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]

private lemma leftEdgePairs_ok : ∀ i : Fin 6,
    barbellK4Graph.Adj (leftEdgePairs i).1 (leftEdgePairs i).2 ∧
      (leftEdgePairs i).1 < (leftEdgePairs i).2 := by
  decide

private lemma rightEdgePairs_ok : ∀ i : Fin 6,
    barbellK4Graph.Adj (rightEdgePairs i).1 (rightEdgePairs i).2 ∧
      (rightEdgePairs i).1 < (rightEdgePairs i).2 := by
  decide

private def barbellOriToFun : Fin 6 ⊕ Unit ⊕ Fin 6 → OriEdge barbellK4Graph
  | .inl i => ⟨leftEdgePairs i, leftEdgePairs_ok i⟩
  | .inr (.inl ()) => ⟨(3, 4), by decide⟩
  | .inr (.inr i) => ⟨rightEdgePairs i, rightEdgePairs_ok i⟩

private def barbellOriInvFun (e : OriEdge barbellK4Graph) : Fin 6 ⊕ Unit ⊕ Fin 6 :=
  match e.1 with
  | (0, 1) => .inl 0 | (0, 2) => .inl 1 | (0, 3) => .inl 2
  | (1, 2) => .inl 3 | (1, 3) => .inl 4 | (2, 3) => .inl 5
  | (3, 4) => .inr (.inl ())
  | (4, 5) => .inr (.inr 0) | (4, 6) => .inr (.inr 1) | (4, 7) => .inr (.inr 2)
  | (5, 6) => .inr (.inr 3) | (5, 7) => .inr (.inr 4) | (6, 7) => .inr (.inr 5)
  | _ => .inr (.inl ())

private def barbellOriEquiv : (Fin 6 ⊕ Unit ⊕ Fin 6) ≃ OriEdge barbellK4Graph where
  toFun := barbellOriToFun
  invFun := barbellOriInvFun
  left_inv x := by rcases x with i | (⟨⟩ | i) <;> [fin_cases i <;> rfl; rfl; fin_cases i <;> rfl]
  right_inv e := Subtype.ext (by
    rcases e with ⟨⟨u, v⟩, h⟩
    fin_cases u <;> fin_cases v <;>
      first | exact False.elim ((by decide : ¬(barbellK4Graph.Adj _ _ ∧ _ < _)) h) | rfl)

private def leftU (L : LeftPerm) : Fin 6 → Fin 8 × Fin 8
  | 0 => (0, barbellNbr 0 (L.1 0))
  | 1 => (0, barbellNbr 0 (L.1 1))
  | 2 => (0, barbellNbr 0 (L.1 2))
  | 3 => (1, barbellNbr 1 (L.2.1 1))
  | 4 => (1, barbellNbr 1 (L.2.1 2))
  | 5 => (2, barbellNbr 2 (L.2.2.1 2))

private def leftV (L : LeftPerm) : Fin 6 → Fin 8 × Fin 8
  | 0 => (1, barbellNbr 1 (L.2.1 0))
  | 1 => (2, barbellNbr 2 (L.2.2.1 0))
  | 2 => (3, barbellNbr 3 (L.2.2.2 0))
  | 3 => (2, barbellNbr 2 (L.2.2.1 1))
  | 4 => (3, barbellNbr 3 (L.2.2.2 1))
  | 5 => (3, barbellNbr 3 (L.2.2.2 2))

private def rightU (R : RightPerm) : Fin 6 → Fin 8 × Fin 8
  | 0 => (4, barbellNbr 4 (R.1 1))
  | 1 => (4, barbellNbr 4 (R.1 2))
  | 2 => (4, barbellNbr 4 (R.1 3))
  | 3 => (5, barbellNbr 5 (R.2.1 1))
  | 4 => (5, barbellNbr 5 (R.2.1 2))
  | 5 => (6, barbellNbr 6 (R.2.2.1 2))

private def rightV (R : RightPerm) : Fin 6 → Fin 8 × Fin 8
  | 0 => (5, barbellNbr 5 (R.2.1 0))
  | 1 => (6, barbellNbr 6 (R.2.2.1 0))
  | 2 => (7, barbellNbr 7 (R.2.2.2 0))
  | 3 => (6, barbellNbr 6 (R.2.2.1 1))
  | 4 => (7, barbellNbr 7 (R.2.2.2 1))
  | 5 => (7, barbellNbr 7 (R.2.2.2 2))

private noncomputable def leftHalfVal (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (k : Fin 2) : ℂ :=
  ∑ L : LeftPerm, ψ 3 (barbellNbr 3 (L.2.2.2 3)) k *
    ∏ i : Fin 6, omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2)

private noncomputable def rightHalfVal (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (k : Fin 2) : ℂ :=
  ∑ R : RightPerm, ψ 4 (barbellNbr 4 (R.1 0)) k *
    ∏ i : Fin 6, omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2)

private lemma barbellSourcePermEquiv_apply (L : LeftPerm) (R : RightPerm) (u w : Fin 8)
    (hw : barbellK4Graph.Adj u w) :
    (barbellSourcePermEquiv (L, R) u ⟨w, hw⟩).1 =
      barbellNbr u ((leftRightPiEquiv (L, R) u) (barbellNbrIdx u w)) := by
  simp [barbellSourcePermEquiv, Equiv.piCongrRight_apply, Equiv.permCongr_apply, barbellNbrEquiv]

private lemma barbell_term_edge (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (L : LeftPerm) (R : RightPerm)
    (e : OriEdge barbellK4Graph) :
    let σ := barbellSourcePermEquiv (L, R)
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ e.1.1 (barbellNbr e.1.1 ((leftRightPiEquiv (L, R) e.1.1) (barbellNbrIdx e.1.1 e.1.2))))
            (ψ e.1.2 (barbellNbr e.1.2 ((leftRightPiEquiv (L, R) e.1.2) (barbellNbrIdx e.1.2 e.1.1)))) := by
  intro σ
  rw [barbellSourcePermEquiv_apply, barbellSourcePermEquiv_apply]

private lemma barbell_term_left (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (L : LeftPerm) (R : RightPerm)
    (i : Fin 6) :
    let σ := barbellSourcePermEquiv (L, R)
    let e := barbellOriEquiv (.inl i)
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2) := by
  dsimp only
  rw [barbell_term_edge]
  fin_cases i <;> rfl

private lemma barbell_term_right (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (L : LeftPerm) (R : RightPerm)
    (i : Fin 6) :
    let σ := barbellSourcePermEquiv (L, R)
    let e := barbellOriEquiv (.inr (.inr i))
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2) := by
  dsimp only
  rw [barbell_term_edge]
  fin_cases i <;> rfl

/-- Bridge factorization across `{3, 4}` for `malkounNum barbellK4Graph`. -/
theorem malkounNum_barbell_bridge (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) :
    malkounNum barbellK4Graph ψ =
      leftHalfVal ψ 0 * rightHalfVal ψ 1 - leftHalfVal ψ 1 * rightHalfVal ψ 0 := by
  unfold malkounNum
  rw [← Fintype.sum_equiv barbellSourcePermEquiv
    (fun p => ∏ e : OriEdge barbellK4Graph,
      omega (ψ e.1.1 ((barbellSourcePermEquiv p) e.1.1 ⟨e.1.2, e.2.1⟩).1)
            (ψ e.1.2 ((barbellSourcePermEquiv p) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
    (fun σ => ∏ e : OriEdge barbellK4Graph,
      omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
    (fun _ => rfl)]
  have hprod : ∀ (L : LeftPerm) (R : RightPerm),
      (∏ e : OriEdge barbellK4Graph,
        omega (ψ e.1.1 ((barbellSourcePermEquiv (L, R)) e.1.1 ⟨e.1.2, e.2.1⟩).1)
              (ψ e.1.2 ((barbellSourcePermEquiv (L, R)) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)) =
      (ψ 3 (barbellNbr 3 (L.2.2.2 3)) 0 *
          ∏ i : Fin 6, omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2)) *
        (ψ 4 (barbellNbr 4 (R.1 0)) 1 *
          ∏ i : Fin 6, omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2)) -
      (ψ 3 (barbellNbr 3 (L.2.2.2 3)) 1 *
          ∏ i : Fin 6, omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2)) *
        (ψ 4 (barbellNbr 4 (R.1 0)) 0 *
          ∏ i : Fin 6, omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2)) := by
    intro L R
    let σ := barbellSourcePermEquiv (L, R)
    rw [← Fintype.prod_equiv barbellOriEquiv
      (fun x => omega (ψ (barbellOriEquiv x).1.1 (σ (barbellOriEquiv x).1.1 ⟨(barbellOriEquiv x).1.2, (barbellOriEquiv x).2.1⟩).1)
                      (ψ (barbellOriEquiv x).1.2 (σ (barbellOriEquiv x).1.2 ⟨(barbellOriEquiv x).1.1, (barbellOriEquiv x).2.1.symm⟩).1))
      (fun e => omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
      (fun _ => rfl)]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    have hl : (∏ i : Fin 6,
        omega (ψ (barbellOriEquiv (.inl i)).1.1 (σ (barbellOriEquiv (.inl i)).1.1 ⟨(barbellOriEquiv (.inl i)).1.2, (barbellOriEquiv (.inl i)).2.1⟩).1)
              (ψ (barbellOriEquiv (.inl i)).1.2 (σ (barbellOriEquiv (.inl i)).1.2 ⟨(barbellOriEquiv (.inl i)).1.1, (barbellOriEquiv (.inl i)).2.1.symm⟩).1)) =
        ∏ i : Fin 6, omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2) :=
      Finset.prod_congr rfl fun i _ => barbell_term_left ψ L R i
    have hr : (∏ i : Fin 6,
        omega (ψ (barbellOriEquiv (.inr (.inr i))).1.1 (σ (barbellOriEquiv (.inr (.inr i))).1.1 ⟨(barbellOriEquiv (.inr (.inr i))).1.2, (barbellOriEquiv (.inr (.inr i))).2.1⟩).1)
              (ψ (barbellOriEquiv (.inr (.inr i))).1.2 (σ (barbellOriEquiv (.inr (.inr i))).1.2 ⟨(barbellOriEquiv (.inr (.inr i))).1.1, (barbellOriEquiv (.inr (.inr i))).2.1.symm⟩).1)) =
        ∏ i : Fin 6, omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2) :=
      Finset.prod_congr rfl fun i _ => barbell_term_right ψ L R i
    have hbridge :
        omega (ψ (barbellOriEquiv (.inr (.inl ()))).1.1 (σ (barbellOriEquiv (.inr (.inl ()))).1.1 ⟨(barbellOriEquiv (.inr (.inl ()))).1.2, (barbellOriEquiv (.inr (.inl ()))).2.1⟩).1)
              (ψ (barbellOriEquiv (.inr (.inl ()))).1.2 (σ (barbellOriEquiv (.inr (.inl ()))).1.2 ⟨(barbellOriEquiv (.inr (.inl ()))).1.1, (barbellOriEquiv (.inr (.inl ()))).2.1.symm⟩).1) =
        omega (ψ 3 (barbellNbr 3 (L.2.2.2 3))) (ψ 4 (barbellNbr 4 (R.1 0))) := by
      dsimp only [σ]
      rw [barbell_term_edge]
      rfl
    rw [hl, hr]
    change (∏ i : Fin 6, omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2)) *
        ((∏ _u : Unit,
          omega (ψ (barbellOriEquiv (.inr (.inl ()))).1.1 (σ (barbellOriEquiv (.inr (.inl ()))).1.1 ⟨(barbellOriEquiv (.inr (.inl ()))).1.2, (barbellOriEquiv (.inr (.inl ()))).2.1⟩).1)
                (ψ (barbellOriEquiv (.inr (.inl ()))).1.2 (σ (barbellOriEquiv (.inr (.inl ()))).1.2 ⟨(barbellOriEquiv (.inr (.inl ()))).1.1, (barbellOriEquiv (.inr (.inl ()))).2.1.symm⟩).1)) *
        (∏ i : Fin 6, omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2))) = _
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one]
    rw [hbridge]
    simp only [omega]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [hprod, Finset.sum_sub_distrib]
  simp only [leftHalfVal, rightHalfVal, Finset.sum_mul_sum]

private def invBit (b : Fin 2) : Fin 2 := 1 - b

private lemma omega_eq_sub_bit (a b : Fin 2 → ℂ) :
    omega a b = (a 0 * b (invBit 0)) - (a 1 * b (invBit 1)) := by
  have h0 : invBit 0 = 1 := by decide
  have h1 : invBit 1 = 0 := by decide
  simp [omega, h0, h1]

private def sgn6C (b : Fin 6 → Fin 2) : ℂ :=
  ∏ i : Fin 6, (if b i = 0 then (1 : ℂ) else -1)

private def vSumC (m : ℕ) (M : Fin m → Fin 2 → ℂ) (c : Fin m → Fin 2) : ℂ :=
  (((bitSum c).factorial * (m - bitSum c).factorial : ℕ) : ℂ) * dickePolyCoeff M (bitSum c)

private lemma sum_prod4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (s : ℂ) (fa : A → ℂ) (fb : B → ℂ) (fc : C → ℂ) (fd : D → ℂ) :
    (∑ p : A × B × C × D, s * fa p.1 * fb p.2.1 * fc p.2.2.1 * fd p.2.2.2) =
      s * (∑ a, fa a) * (∑ b, fb b) * (∑ c, fc c) * (∑ d, fd d) := by
  rw [Fintype.sum_prod_type]
  calc (∑ a : A, ∑ q : B × C × D, s * fa a * fb q.1 * fc q.2.1 * fd q.2.2)
      = ∑ a : A, ∑ b : B, ∑ r : C × D, s * fa a * fb b * fc r.1 * fd r.2 :=
          Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _
    _ = ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, s * fa a * fb b * fc c * fd d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Fintype.sum_prod_type _
    _ = ∑ a : A, ∑ b : B, ∑ c : C, s * fa a * fb b * fc c * ∑ d : D, fd d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ a : A, ∑ b : B, (∑ c : C, s * fa a * fb b * fc c) * ∑ d : D, fd d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            (Finset.sum_mul _ _ _).symm
    _ = ∑ a : A, ∑ b : B, (s * fa a * fb b * ∑ c : C, fc c) * ∑ d : D, fd d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            congrArg (· * ∑ d, fd d) (Finset.mul_sum _ _ _).symm
    _ = ∑ a : A, (s * fa a * ∑ b : B, fb b) * (∑ c : C, fc c) * ∑ d : D, fd d := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact (Finset.mul_sum _ _ _).symm
    _ = s * (∑ a : A, fa a) * (∑ b : B, fb b) * (∑ c : C, fc c) * ∑ d : D, fd d := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
          congr 3
          exact (Finset.mul_sum _ _ _).symm

private lemma leftHalfVal_eq_sumBits (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (k : Fin 2) :
    leftHalfVal ψ k = sumBits 6 fun b =>
      sgn6C b *
      vSumC 3 (fun j => ψ 0 (barbellNbr 0 j)) ![b 0, b 1, b 2] *
      vSumC 3 (fun j => ψ 1 (barbellNbr 1 j)) ![invBit (b 0), b 3, b 4] *
      vSumC 3 (fun j => ψ 2 (barbellNbr 2 j)) ![invBit (b 1), invBit (b 3), b 5] *
      vSumC 4 (fun j => ψ 3 (barbellNbr 3 j)) ![invBit (b 2), invBit (b 4), invBit (b 5), k] := by
  rw [← sum_bitFun_eq_sumBits 6]
  unfold leftHalfVal
  have hexp : ∀ L : LeftPerm,
      (ψ 3 (barbellNbr 3 (L.2.2.2 3)) k *
        ∏ i : Fin 6, omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2)) =
      ∑ b : Fin 6 → Fin 2,
        sgn6C b *
        (∏ j : Fin 3, ψ 0 (barbellNbr 0 (L.1 j)) (![b 0, b 1, b 2] j)) *
        (∏ j : Fin 3, ψ 1 (barbellNbr 1 (L.2.1 j)) (![invBit (b 0), b 3, b 4] j)) *
        (∏ j : Fin 3, ψ 2 (barbellNbr 2 (L.2.2.1 j)) (![invBit (b 1), invBit (b 3), b 5] j)) *
        (∏ j : Fin 4, ψ 3 (barbellNbr 3 (L.2.2.2 j)) (![invBit (b 2), invBit (b 4), invBit (b 5), k] j)) := by
    intro L
    have homega : ∀ i : Fin 6,
        omega (ψ (leftU L i).1 (leftU L i).2) (ψ (leftV L i).1 (leftV L i).2) =
        (ψ (leftU L i).1 (leftU L i).2 0 * ψ (leftV L i).1 (leftV L i).2 (invBit 0)) -
        (ψ (leftU L i).1 (leftU L i).2 1 * ψ (leftV L i).1 (leftV L i).2 (invBit 1)) :=
      fun i => omega_eq_sub_bit _ _
    simp_rw [homega]
    rw [prod_fin2_sub_eq_sumBits 6
      (fun i bit => ψ (leftU L i).1 (leftU L i).2 bit * ψ (leftV L i).1 (leftV L i).2 (invBit bit))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [sgn6C, Fin.prod_univ_six, Fin.prod_univ_three, Fin.prod_univ_four,
      leftU, leftV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfac := sum_prod4 (sgn6C b)
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 0 (barbellNbr 0 (a j)) (![b 0, b 1, b 2] j))
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 1 (barbellNbr 1 (a j)) (![invBit (b 0), b 3, b 4] j))
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 2 (barbellNbr 2 (a j)) (![invBit (b 1), invBit (b 3), b 5] j))
    (fun a : Equiv.Perm (Fin 4) => ∏ j : Fin 4, ψ 3 (barbellNbr 3 (a j)) (![invBit (b 2), invBit (b 4), invBit (b 5), k] j))
  rw [hfac,
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 0 (barbellNbr 0 j)) ![b 0, b 1, b 2],
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 1 (barbellNbr 1 j)) ![invBit (b 0), b 3, b 4],
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 2 (barbellNbr 2 j)) ![invBit (b 1), invBit (b 3), b 5],
    perm_sigma_sum_eq_dicke 4 (fun j => ψ 3 (barbellNbr 3 j)) ![invBit (b 2), invBit (b 4), invBit (b 5), k]]
  simp only [vSumC]

private lemma rightHalfVal_eq_sumBits (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (k : Fin 2) :
    rightHalfVal ψ k = sumBits 6 fun b =>
      sgn6C b *
      vSumC 4 (fun j => ψ 4 (barbellNbr 4 j)) ![k, b 0, b 1, b 2] *
      vSumC 3 (fun j => ψ 5 (barbellNbr 5 j)) ![invBit (b 0), b 3, b 4] *
      vSumC 3 (fun j => ψ 6 (barbellNbr 6 j)) ![invBit (b 1), invBit (b 3), b 5] *
      vSumC 3 (fun j => ψ 7 (barbellNbr 7 j)) ![invBit (b 2), invBit (b 4), invBit (b 5)] := by
  rw [← sum_bitFun_eq_sumBits 6]
  unfold rightHalfVal
  have hexp : ∀ R : RightPerm,
      (ψ 4 (barbellNbr 4 (R.1 0)) k *
        ∏ i : Fin 6, omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2)) =
      ∑ b : Fin 6 → Fin 2,
        sgn6C b *
        (∏ j : Fin 4, ψ 4 (barbellNbr 4 (R.1 j)) (![k, b 0, b 1, b 2] j)) *
        (∏ j : Fin 3, ψ 5 (barbellNbr 5 (R.2.1 j)) (![invBit (b 0), b 3, b 4] j)) *
        (∏ j : Fin 3, ψ 6 (barbellNbr 6 (R.2.2.1 j)) (![invBit (b 1), invBit (b 3), b 5] j)) *
        (∏ j : Fin 3, ψ 7 (barbellNbr 7 (R.2.2.2 j)) (![invBit (b 2), invBit (b 4), invBit (b 5)] j)) := by
    intro R
    have homega : ∀ i : Fin 6,
        omega (ψ (rightU R i).1 (rightU R i).2) (ψ (rightV R i).1 (rightV R i).2) =
        (ψ (rightU R i).1 (rightU R i).2 0 * ψ (rightV R i).1 (rightV R i).2 (invBit 0)) -
        (ψ (rightU R i).1 (rightU R i).2 1 * ψ (rightV R i).1 (rightV R i).2 (invBit 1)) :=
      fun i => omega_eq_sub_bit _ _
    simp_rw [homega]
    rw [prod_fin2_sub_eq_sumBits 6
      (fun i bit => ψ (rightU R i).1 (rightU R i).2 bit * ψ (rightV R i).1 (rightV R i).2 (invBit bit))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [sgn6C, Fin.prod_univ_six, Fin.prod_univ_three, Fin.prod_univ_four,
      rightU, rightV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfac := sum_prod4 (sgn6C b)
    (fun a : Equiv.Perm (Fin 4) => ∏ j : Fin 4, ψ 4 (barbellNbr 4 (a j)) (![k, b 0, b 1, b 2] j))
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 5 (barbellNbr 5 (a j)) (![invBit (b 0), b 3, b 4] j))
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 6 (barbellNbr 6 (a j)) (![invBit (b 1), invBit (b 3), b 5] j))
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 7 (barbellNbr 7 (a j)) (![invBit (b 2), invBit (b 4), invBit (b 5)] j))
  rw [hfac,
    perm_sigma_sum_eq_dicke 4 (fun j => ψ 4 (barbellNbr 4 j)) ![k, b 0, b 1, b 2],
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 5 (barbellNbr 5 j)) ![invBit (b 0), b 3, b 4],
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 6 (barbellNbr 6 j)) ![invBit (b 1), invBit (b 3), b 5],
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 7 (barbellNbr 7 j)) ![invBit (b 2), invBit (b 4), invBit (b 5)]]
  simp only [vSumC]

/-! ### Pure Computable `GI` Evaluator and Kernel-Verified Certificates -/

def invBitNat (b : Fin 2) : ℕ := if b = 0 then 1 else 0

private lemma invBit_val (b : Fin 2) : (invBit b).val = invBitNat b := by
  fin_cases b <;> rfl

private lemma bitSum3_eq (a b c : Fin 2) :
    bitSum ![a, b, c] = a.val + b.val + c.val := by
  simp [bitSum, Fin.sum_univ_three, add_assoc]

private lemma bitSum4_eq (a b c d : Fin 2) :
    bitSum ![a, b, c, d] = a.val + b.val + c.val + d.val := by
  simp [bitSum, Fin.sum_univ_four, add_assoc]

def sgn6GI (b : Fin 6 → Fin 2) : GI :=
  let s (x : Fin 2) : ℤ := if x = 0 then 1 else -1
  GI.ofInt (s (b 0) * s (b 1) * s (b 2) * s (b 3) * s (b 4) * s (b 5))

private lemma toC_sgn6GI (b : Fin 6 → Fin 2) : GI.toC (sgn6GI b) = sgn6C b := by
  simp only [sgn6GI, sgn6C, GI.toC_ofInt, Fin.prod_univ_six]
  push_cast
  rfl

def factWeight3 : ℕ → ℤ
  | 0 => 6 | 1 => 2 | 2 => 2 | _ => 6

def factWeight4 : ℕ → ℤ
  | 0 => 24 | 1 => 6 | 2 => 4 | 3 => 6 | _ => 24

private lemma factWeight3_eq (w : ℕ) (hw : w ≤ 3) :
    (w.factorial * (3 - w).factorial : ℕ) = (factWeight3 w : ℤ) := by
  interval_cases w <;> decide

private lemma factWeight4_eq (w : ℕ) (hw : w ≤ 4) :
    (w.factorial * (4 - w).factorial : ℕ) = (factWeight4 w : ℤ) := by
  interval_cases w <;> decide

def vTab3GI (M : Fin 3 → Fin 2 → GI) : ℕ → GI
  | 0 => GI.ofInt 6 * GI.dickePolyCoeffGI M 0
  | 1 => GI.ofInt 2 * GI.dickePolyCoeffGI M 1
  | 2 => GI.ofInt 2 * GI.dickePolyCoeffGI M 2
  | _ => GI.ofInt 6 * GI.dickePolyCoeffGI M 3

def vTab4GI (M : Fin 4 → Fin 2 → GI) : ℕ → GI
  | 0 => GI.ofInt 24 * GI.dickePolyCoeffGI M 0
  | 1 => GI.ofInt 6 * GI.dickePolyCoeffGI M 1
  | 2 => GI.ofInt 4 * GI.dickePolyCoeffGI M 2
  | 3 => GI.ofInt 6 * GI.dickePolyCoeffGI M 3
  | _ => GI.ofInt 24 * GI.dickePolyCoeffGI M 4

private lemma toC_vTab3GI (M : Fin 3 → Fin 2 → GI) (c : Fin 3 → Fin 2) :
    GI.toC (vTab3GI M (bitSum c)) = vSumC 3 (fun i k => GI.toC (M i k)) c := by
  have hle : bitSum c ≤ 3 := bitSum_le c
  rcases h0 : bitSum c with _ | _ | _ | _ | w
  all_goals
    simp only [vTab3GI, vSumC, h0, GI.toC_mul, GI.toC_ofInt, GI.toC_dickePolyCoeffGI]
  all_goals
    first | (dsimp; norm_num) | omega

private lemma toC_vTab4GI (M : Fin 4 → Fin 2 → GI) (c : Fin 4 → Fin 2) :
    GI.toC (vTab4GI M (bitSum c)) = vSumC 4 (fun i k => GI.toC (M i k)) c := by
  have hle : bitSum c ≤ 4 := bitSum_le c
  rcases h0 : bitSum c with _ | _ | _ | _ | _ | w
  all_goals
    simp only [vTab4GI, vSumC, h0, GI.toC_mul, GI.toC_ofInt, GI.toC_dickePolyCoeffGI]
  all_goals
    first | (dsimp; norm_num) | omega

def leftHalfGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) (k : Fin 2) : GI :=
  let t0 := vTab3GI (fun j => ψ 0 (barbellNbr 0 j))
  let t1 := vTab3GI (fun j => ψ 1 (barbellNbr 1 j))
  let t2 := vTab3GI (fun j => ψ 2 (barbellNbr 2 j))
  let t3 := vTab4GI (fun j => ψ 3 (barbellNbr 3 j))
  sumBits 6 fun b =>
    sgn6GI b *
    t0 ((b 0).val + (b 1).val + (b 2).val) *
    t1 (invBitNat (b 0) + (b 3).val + (b 4).val) *
    t2 (invBitNat (b 1) + invBitNat (b 3) + (b 5).val) *
    t3 (invBitNat (b 2) + invBitNat (b 4) + invBitNat (b 5) + k.val)

def rightHalfGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) (k : Fin 2) : GI :=
  let t4 := vTab4GI (fun j => ψ 4 (barbellNbr 4 j))
  let t5 := vTab3GI (fun j => ψ 5 (barbellNbr 5 j))
  let t6 := vTab3GI (fun j => ψ 6 (barbellNbr 6 j))
  let t7 := vTab3GI (fun j => ψ 7 (barbellNbr 7 j))
  sumBits 6 fun b =>
    sgn6GI b *
    t4 (k.val + (b 0).val + (b 1).val + (b 2).val) *
    t5 (invBitNat (b 0) + (b 3).val + (b 4).val) *
    t6 (invBitNat (b 1) + invBitNat (b 3) + (b 5).val) *
    t7 (invBitNat (b 2) + invBitNat (b 4) + invBitNat (b 5))

def omegaGI (a b : Fin 2 → GI) : GI := a 0 * b 1 - a 1 * b 0

@[simp] lemma toC_omegaGI (a b : Fin 2 → GI) :
    GI.toC (omegaGI a b) = omega (fun k => GI.toC (a k)) (fun k => GI.toC (b k)) := by
  simp [omegaGI, omega]

def barbellNumGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) : GI :=
  leftHalfGI ψ 0 * rightHalfGI ψ 1 - leftHalfGI ψ 1 * rightHalfGI ψ 0

def prod6GI (g : Fin 6 → GI) : GI := g 0 * g 1 * g 2 * g 3 * g 4 * g 5

private lemma toC_prod6GI (g : Fin 6 → GI) : GI.toC (prod6GI g) = ∏ i : Fin 6, GI.toC (g i) := by
  rw [Fin.prod_univ_six]
  simp [prod6GI]

def barbellDenGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) : GI :=
  prod6GI (fun i => omegaGI (ψ (leftEdgePairs i).1 (leftEdgePairs i).2)
                            (ψ (leftEdgePairs i).2 (leftEdgePairs i).1)) *
  omegaGI (ψ 3 4) (ψ 4 3) *
  prod6GI (fun i => omegaGI (ψ (rightEdgePairs i).1 (rightEdgePairs i).2)
                            (ψ (rightEdgePairs i).2 (rightEdgePairs i).1))

private lemma sumBits_congr {R : Type*} [Add R] :
    ∀ (m : ℕ) {f g : (Fin m → Fin 2) → R}, (∀ b, f b = g b) → sumBits m f = sumBits m g
  | 0, _, _, h => h Fin.elim0
  | m + 1, _, _, h => by
      simp only [sumBits]
      rw [sumBits_congr m (fun f => h (Fin.cons 0 f)),
          sumBits_congr m (fun f => h (Fin.cons 1 f))]

theorem malkounNum_barbell_giToC (ψ : Fin 8 → Fin 8 → Fin 2 → GI) :
    GI.toC (barbellNumGI ψ) = malkounNum barbellK4Graph (fun u v k => GI.toC (ψ u v k)) := by
  have hl : ∀ k, GI.toC (leftHalfGI ψ k) = leftHalfVal (fun u v k => GI.toC (ψ u v k)) k := by
    intro k
    rw [leftHalfVal_eq_sumBits, leftHalfGI, GI.toC_sumBits]
    refine sumBits_congr 6 fun b => ?_
    simp only [GI.toC_mul, toC_sgn6GI]
    rw [← bitSum3_eq, ← invBit_val (b 0), ← bitSum3_eq,
        ← invBit_val (b 1), ← invBit_val (b 3), ← bitSum3_eq,
        ← invBit_val (b 2), ← invBit_val (b 4), ← invBit_val (b 5), ← bitSum4_eq]
    simp only [toC_vTab3GI, toC_vTab4GI]
  have hr : ∀ k, GI.toC (rightHalfGI ψ k) = rightHalfVal (fun u v k => GI.toC (ψ u v k)) k := by
    intro k
    rw [rightHalfVal_eq_sumBits, rightHalfGI, GI.toC_sumBits]
    refine sumBits_congr 6 fun b => ?_
    simp only [GI.toC_mul, toC_sgn6GI]
    rw [← bitSum4_eq, ← invBit_val (b 0), ← bitSum3_eq,
        ← invBit_val (b 1), ← invBit_val (b 3), ← bitSum3_eq,
        ← invBit_val (b 2), ← invBit_val (b 4), ← invBit_val (b 5), ← bitSum3_eq]
    simp only [toC_vTab3GI, toC_vTab4GI]
  rw [malkounNum_barbell_bridge, barbellNumGI, GI.toC_sub, GI.toC_mul, GI.toC_mul, hl 0, hr 1, hl 1, hr 0]

theorem malkounDen_barbell_giToC (ψ : Fin 8 → Fin 8 → Fin 2 → GI) :
    GI.toC (barbellDenGI ψ) = malkounDen barbellK4Graph (fun u v k => GI.toC (ψ u v k)) := by
  unfold malkounDen barbellDenGI
  rw [← Fintype.prod_equiv barbellOriEquiv
    (fun x => omega (fun k => GI.toC (ψ (barbellOriEquiv x).1.1 (barbellOriEquiv x).1.2 k))
                    (fun k => GI.toC (ψ (barbellOriEquiv x).1.2 (barbellOriEquiv x).1.1 k)))
    (fun e => omega (fun k => GI.toC (ψ e.1.1 e.1.2 k)) (fun k => GI.toC (ψ e.1.2 e.1.1 k)))
    (fun _ => rfl)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  have hleft :
      (∏ i : Fin 6,
        omega (fun k => GI.toC (ψ (barbellOriEquiv (.inl i)).1.1 (barbellOriEquiv (.inl i)).1.2 k))
              (fun k => GI.toC (ψ (barbellOriEquiv (.inl i)).1.2 (barbellOriEquiv (.inl i)).1.1 k))) =
      GI.toC (prod6GI fun i => omegaGI (ψ (leftEdgePairs i).1 (leftEdgePairs i).2)
                                       (ψ (leftEdgePairs i).2 (leftEdgePairs i).1)) := by
    rw [toC_prod6GI]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [barbellOriEquiv, barbellOriToFun]
  have hmid :
      (∏ _u : Unit,
        omega (fun k => GI.toC (ψ (barbellOriEquiv (.inr (.inl ()))).1.1 (barbellOriEquiv (.inr (.inl ()))).1.2 k))
              (fun k => GI.toC (ψ (barbellOriEquiv (.inr (.inl ()))).1.2 (barbellOriEquiv (.inr (.inl ()))).1.1 k))) =
      GI.toC (omegaGI (ψ 3 4) (ψ 4 3)) := by
    simp [barbellOriEquiv, barbellOriToFun]
  have hright :
      (∏ i : Fin 6,
        omega (fun k => GI.toC (ψ (barbellOriEquiv (.inr (.inr i))).1.1 (barbellOriEquiv (.inr (.inr i))).1.2 k))
              (fun k => GI.toC (ψ (barbellOriEquiv (.inr (.inr i))).1.2 (barbellOriEquiv (.inr (.inr i))).1.1 k))) =
      GI.toC (prod6GI fun i => omegaGI (ψ (rightEdgePairs i).1 (rightEdgePairs i).2)
                                       (ψ (rightEdgePairs i).2 (rightEdgePairs i).1)) := by
    rw [toC_prod6GI]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [barbellOriEquiv, barbellOriToFun]
  rw [hleft, hmid, hright, GI.toC_mul, GI.toC_mul, mul_assoc]

end BarbellCombinatorics

/-! ### Exact Integer Planar Endpoints & Kernel `decide` Certificates -/

section ExactCertificates

/-- Exact $x$-coordinates of the 8-vertex counterexample. -/
def barbellPtsX : Fin 8 → ℤ := ![-677, -31, -1326, -1, 1, 1326, 677, 31]

/-- Exact $y$-coordinates at $t = 1$ (scaled by $t$ along the homotopy). -/
def barbellPtsY : Fin 8 → ℤ := ![0, 72, 0, 0, 0, 0, 0, 72]

lemma barbellPtsX_inj : Function.Injective barbellPtsX := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp_all [barbellPtsX]

/-- Exact collinear Euclidean distance $|x_v - x_u|$ (avoids `Nat.sqrt` for kernel `decide`). -/
def distColInt (u v : Fin 8) : ℤ :=
  ((barbellPtsX v - barbellPtsX u).natAbs : ℤ)

/-- Exact planar Euclidean distance at $t = 1$ (Pythagorean triples `650`, `1297`, `78` and horizontal edges). -/
def distNegInt (u v : Fin 8) : ℤ :=
  if (u == 0 && v == 1) || (u == 1 && v == 0) || (u == 6 && v == 7) || (u == 7 && v == 6) then 650
  else if (u == 1 && v == 2) || (u == 2 && v == 1) || (u == 5 && v == 7) || (u == 7 && v == 5) then 1297
  else if (u == 1 && v == 3) || (u == 3 && v == 1) || (u == 4 && v == 7) || (u == 7 && v == 4) then 78
  else ((barbellPtsX v - barbellPtsX u).natAbs : ℤ)

def scaleFromInts (r dx dy : ℤ) : ℤ :=
  let g := Nat.gcd r.natAbs (Nat.gcd dx.natAbs dy.natAbs)
  if g = 0 then 1 else (g : ℤ)

def spinorFromInts (r dx dy : ℤ) : Fin 2 → GI
  | 0 => GI.ofInt (r / scaleFromInts r dx dy)
  | 1 => ⟨dx / scaleFromInts r dx dy, dy / scaleFromInts r dx dy⟩

def spinorsColGI (u v : Fin 8) : Fin 2 → GI :=
  spinorFromInts (distColInt u v) (barbellPtsX v - barbellPtsX u) 0

def spinorsNegGI (u v : Fin 8) : Fin 2 → GI :=
  spinorFromInts (distNegInt u v) (barbellPtsX v - barbellPtsX u) (barbellPtsY v - barbellPtsY u)

lemma spinorsColGI_ok : ∀ u v : Fin 8, barbellK4Graph.Adj u v →
    let dx := barbellPtsX v - barbellPtsX u
    let r := distColInt u v
    let g := scaleFromInts r dx 0
    g ≠ 0 ∧ 0 ≤ r ∧ r * r = dx * dx ∧
    r = g * (spinorsColGI u v 0).re ∧
    (spinorsColGI u v 0).im = 0 ∧
    dx = g * (spinorsColGI u v 1).re ∧
    0 = g * (spinorsColGI u v 1).im := by
  decide

lemma spinorsNegGI_ok : ∀ u v : Fin 8, barbellK4Graph.Adj u v →
    let dx := barbellPtsX v - barbellPtsX u
    let dy := barbellPtsY v - barbellPtsY u
    let r := distNegInt u v
    let g := scaleFromInts r dx dy
    g ≠ 0 ∧ 0 ≤ r ∧ r * r = dx * dx + dy * dy ∧
    r = g * (spinorsNegGI u v 0).re ∧
    (spinorsNegGI u v 0).im = 0 ∧
    dx = g * (spinorsNegGI u v 1).re ∧
    dy = g * (spinorsNegGI u v 1).im := by
  decide

/-- Kernel-verified $t=0$ collinear numerator (`169869312`). -/
theorem cert_col_num : barbellNumGI spinorsColGI = GI.ofInt 169869312 := by
  decide

/-- Kernel-verified $t=0$ collinear denominator (`8192`, ratio $= +20736$). -/
theorem cert_col_den : barbellDenGI spinorsColGI = GI.ofInt 8192 := by
  decide

/-- Kernel-verified $t=1$ planar numerator (`-421510357090419997394451824640000`). -/
theorem cert_neg_num :
    barbellNumGI spinorsNegGI = GI.ofInt (-421510357090419997394451824640000) := by
  decide

/-- Kernel-verified $t=1$ planar denominator (`7386806133256753344003200000000`). -/
theorem cert_neg_den :
    barbellDenGI spinorsNegGI = GI.ofInt 7386806133256753344003200000000 := by
  decide

end ExactCertificates

/-! ## Part 4: Collision-Free Homotopy, Continuity, IVT, and Formal Disproofs -/

section HomotopyDisproof

/-- Continuous planar path $\gamma(t)$ ($t \in \mathbb{R}$) in $\mathbb{R}^3$:
collinear configuration at $t = 0$ ($\mathcal{A}_G = +20736$) and planar non-collinear configuration
at $t = 1$ ($\mathcal{A}_G = -1713503232016128 / 30028482030625$). -/
def barbellPoint (t : ℝ) (u : Fin 8) : Fin 3 → ℝ
  | 0 => (barbellPtsX u : ℝ)
  | 1 => (barbellPtsY u : ℝ) * t
  | 2 => 0

/-- For every $t \in \mathbb{R}$, `barbellPoint t` has pairwise distinct $x$-coordinates and thus
lies in $C_G(\mathbb{R}^3)$ for `barbellK4Graph`. -/
def barbellPath (t : ℝ) : ConfigSpace barbellK4Graph :=
  ⟨barbellPoint t, by
    intro u v huv h
    have hx : (barbellPtsX u : ℝ) = (barbellPtsX v : ℝ) := congr_fun h 0
    exact barbellK4Graph.ne_of_adj huv (barbellPtsX_inj (Int.cast_injective hx))⟩

lemma barbellPath_planar (t : ℝ) (u : Fin 8) : (barbellPath t).1 u 2 = 0 := rfl

private lemma malkounAmplitudeOfSpinors_congr {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (ψ₁ ψ₂ : Fin m → Fin m → Fin 2 → ℂ)
    (h : ∀ u v, G.Adj u v → ∀ k, ψ₁ u v k = ψ₂ u v k) :
    malkounAmplitudeOfSpinors G ψ₁ = malkounAmplitudeOfSpinors G ψ₂ := by
  have h1 : ∀ u v, G.Adj u v → ψ₁ u v = ψ₂ u v := fun u v huv => funext (h u v huv)
  have hnum : malkounNum G ψ₁ = malkounNum G ψ₂ := by
    refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => ?_
    rw [h1 _ _ (σ e.1.1 ⟨e.1.2, e.2.1⟩).2, h1 _ _ (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).2]
  have hden : malkounDen G ψ₁ = malkounDen G ψ₂ := by
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [h1 _ _ e.2.1, h1 _ _ e.2.1.symm]
  simp only [malkounAmplitudeOfSpinors, hnum, hden]

private lemma barbell_amplitude_of_spinorGI (t : ℝ) (ψ : Fin 8 → Fin 8 → Fin 2 → GI)
    (scale : Fin 8 → Fin 8 → ℤ)
    (hscale : ∀ u v, barbellK4Graph.Adj u v → scale u v ≠ 0)
    (hmatch : ∀ u v, barbellK4Graph.Adj u v → ∀ k,
      planarUnnormSpinor (barbellPoint t u) (barbellPoint t v) k =
        ((scale u v : ℤ) : ℂ) * GI.toC (ψ u v k)) :
    malkounAmplitude barbellK4Graph (barbellPath t) =
      GI.toC (barbellNumGI ψ) / GI.toC (barbellDenGI ψ) := by
  rw [malkounAmplitude_eq_planarUnnorm barbellK4Graph (barbellPath t) (barbellPath_planar t)]
  change malkounAmplitudeOfSpinors barbellK4Graph
      (fun u v => planarUnnormSpinor (barbellPoint t u) (barbellPoint t v)) = _
  rw [malkounAmplitudeOfSpinors_congr barbellK4Graph _
      (fun u v k => ((scale u v : ℤ) : ℂ) * GI.toC (ψ u v k)) hmatch]
  rw [malkounAmplitude_scale_invariant barbellK4Graph (fun u v => ((scale u v : ℤ) : ℂ))
      (fun u v huv => Int.cast_ne_zero.mpr (hscale u v huv)) (fun u v k => GI.toC (ψ u v k))]
  simp only [malkounAmplitudeOfSpinors, malkounNum_barbell_giToC, malkounDen_barbell_giToC]

private lemma match_planar_endpoint (t : ℝ) (dx dy r g : ℤ) (s : Fin 2 → GI)
    (hr_nn : 0 ≤ r)
    (hpt0 : barbellPoint t v 0 - barbellPoint t u 0 = (dx : ℝ))
    (hpt1 : barbellPoint t v 1 - barbellPoint t u 1 = (dy : ℝ))
    (hr_sq : r * r = dx * dx + dy * dy)
    (h0re : r = g * (s 0).re) (h0im : (s 0).im = 0)
    (h1re : dx = g * (s 1).re) (h1im : dy = g * (s 1).im) :
    ∀ k : Fin 2, planarUnnormSpinor (barbellPoint t u) (barbellPoint t v) k =
      ((g : ℤ) : ℂ) * GI.toC (s k) := by
  have hr_R : (r : ℝ) ^ 2 = (barbellPoint t v 0 - barbellPoint t u 0) ^ 2 +
      (barbellPoint t v 1 - barbellPoint t u 1) ^ 2 +
      (barbellPoint t v 2 - barbellPoint t u 2) ^ 2 := by
    rw [hpt0, hpt1]
    simp only [barbellPoint, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    have hsq : (r : ℝ) * (r : ℝ) = (dx : ℝ) * (dx : ℝ) + (dy : ℝ) * (dy : ℝ) := by exact_mod_cast hr_sq
    linarith [sq (r : ℝ), sq (dx : ℝ), sq (dy : ℝ)]
  have heuclid : euclidNorm (fun j => barbellPoint t v j - barbellPoint t u j) = (r : ℝ) := by
    rw [euclidNorm, ← hr_R]
    exact Real.sqrt_sq (by exact_mod_cast hr_nn)
  intro k
  rcases fin2_cases k with rfl | rfl
  · simp only [planarUnnormSpinor, heuclid, GI.toC, h0im, Int.cast_zero, mul_zero, add_zero]
    exact_mod_cast h0re
  · simp only [planarUnnormSpinor, hpt0, hpt1, GI.toC]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.intCast_re,
        Complex.intCast_im, sub_zero]
      exact_mod_cast h1re
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_re, one_mul, zero_add, Complex.intCast_im,
        Complex.intCast_re, mul_zero, add_zero]
      exact_mod_cast h1im

/-- Exact value at $t = 0$: collinear 8-vertex barbell has amplitude $+20736$. -/
theorem malkounAmplitude_barbellPath_zero :
    malkounAmplitude barbellK4Graph (barbellPath 0) = 20736 := by
  have heq : malkounAmplitude barbellK4Graph (barbellPath 0) =
      GI.toC (barbellNumGI spinorsColGI) / GI.toC (barbellDenGI spinorsColGI) := by
    refine barbell_amplitude_of_spinorGI 0 spinorsColGI
      (fun u v => scaleFromInts (distColInt u v) (barbellPtsX v - barbellPtsX u) 0)
      (fun u v huv => (spinorsColGI_ok u v huv).1) fun u v huv => ?_
    rcases spinorsColGI_ok u v huv with ⟨_, hr_nn, hr_sq, h0re, h0im, h1re, h1im⟩
    exact match_planar_endpoint 0 (barbellPtsX v - barbellPtsX u) 0 (distColInt u v)
      (scaleFromInts (distColInt u v) (barbellPtsX v - barbellPtsX u) 0) (spinorsColGI u v)
      hr_nn (by simp [barbellPoint]) (by simp [barbellPoint])
      (by simpa [mul_zero, add_zero] using hr_sq) h0re h0im h1re h1im
  rw [heq, cert_col_num, cert_col_den, GI.toC_ofInt, GI.toC_ofInt]
  norm_num

/-- Exact rational value at $t = 1$: $-1713503232016128 / 30028482030625 < 0$. -/
theorem malkounAmplitude_barbellPath_one :
    malkounAmplitude barbellK4Graph (barbellPath 1) =
      (-1713503232016128 / 30028482030625 : ℂ) := by
  have heq : malkounAmplitude barbellK4Graph (barbellPath 1) =
      GI.toC (barbellNumGI spinorsNegGI) / GI.toC (barbellDenGI spinorsNegGI) := by
    refine barbell_amplitude_of_spinorGI 1 spinorsNegGI
      (fun u v => scaleFromInts (distNegInt u v) (barbellPtsX v - barbellPtsX u)
        (barbellPtsY v - barbellPtsY u))
      (fun u v huv => (spinorsNegGI_ok u v huv).1) fun u v huv => ?_
    rcases spinorsNegGI_ok u v huv with ⟨_, hr_nn, hr_sq, h0re, h0im, h1re, h1im⟩
    exact match_planar_endpoint 1 (barbellPtsX v - barbellPtsX u) (barbellPtsY v - barbellPtsY u)
      (distNegInt u v)
      (scaleFromInts (distNegInt u v) (barbellPtsX v - barbellPtsX u)
        (barbellPtsY v - barbellPtsY u))
      (spinorsNegGI u v) hr_nn (by simp [barbellPoint])
      (by simp [barbellPoint, Int.cast_sub]) hr_sq h0re h0im h1re h1im
  rw [heq, cert_neg_num, cert_neg_den, GI.toC_ofInt, GI.toC_ofInt]
  norm_num

private lemma continuous_planarUnnorm_barbellPath (u v : Fin 8) (k : Fin 2) :
    Continuous (fun t : ℝ => planarUnnormSpinor (barbellPoint t u) (barbellPoint t v) k) := by
  fin_cases k
  · dsimp [planarUnnormSpinor, euclidNorm, barbellPoint]
    fun_prop
  · dsimp [planarUnnormSpinor, barbellPoint]
    fun_prop

theorem continuous_malkounAmplitude_barbellPath :
    Continuous (fun t : ℝ => malkounAmplitude barbellK4Graph (barbellPath t)) := by
  have hfun : (fun t : ℝ => malkounAmplitude barbellK4Graph (barbellPath t)) =
      fun t : ℝ =>
        malkounNum barbellK4Graph (fun u v => planarUnnormSpinor (barbellPoint t u) (barbellPoint t v)) /
        malkounDen barbellK4Graph (fun u v => planarUnnormSpinor (barbellPoint t u) (barbellPoint t v)) := by
    ext t
    exact malkounAmplitude_eq_planarUnnorm barbellK4Graph (barbellPath t) (barbellPath_planar t)
  rw [hfun]
  have hspin : ∀ u v k,
      Continuous (fun t : ℝ => planarUnnormSpinor (barbellPoint t u) (barbellPoint t v) k) :=
    continuous_planarUnnorm_barbellPath
  have homega : ∀ (f g : Fin 2 → ℝ → ℂ), (∀ k, Continuous (f k)) → (∀ k, Continuous (g k)) →
      Continuous (fun t => omega (fun k => f k t) (fun k => g k t)) := by
    intro f g hf hg
    dsimp [omega]
    fun_prop
  have hnum : Continuous (fun t : ℝ =>
      malkounNum barbellK4Graph (fun u v => planarUnnormSpinor (barbellPoint t u) (barbellPoint t v))) := by
    dsimp [malkounNum]
    fun_prop (disch := exact fun _ _ _ => _)
  have hden : Continuous (fun t : ℝ =>
      malkounDen barbellK4Graph (fun u v => planarUnnormSpinor (barbellPoint t u) (barbellPoint t v))) := by
    dsimp [malkounDen]
    fun_prop
  exact hnum.div hden fun t =>
    malkounDen_planarUnnorm_ne_zero barbellK4Graph (barbellPath t) (barbellPath_planar t)

private lemma exists_barbellPath_zero :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) 1, malkounAmplitude barbellK4Graph (barbellPath t₀) = 0 := by
  let f : ℝ → ℝ := fun t => (malkounAmplitude barbellK4Graph (barbellPath t)).re
  have hf_cont : Continuous f := Complex.continuous_re.comp continuous_malkounAmplitude_barbellPath
  have h0 : f 0 = 20736 := by
    dsimp [f]
    rw [malkounAmplitude_barbellPath_zero]
    norm_num
  have h1 : f 1 = -1713503232016128 / 30028482030625 := by
    dsimp [f]
    rw [malkounAmplitude_barbellPath_one]
    norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
    rw [h0, h1]
    constructor <;> norm_num
  rcases intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf_cont.continuousOn hmem with
    ⟨t₀, ht₀_icc, ht₀_re⟩
  refine ⟨t₀, ht₀_icc, ?_⟩
  have ht₀_im : (malkounAmplitude barbellK4Graph (barbellPath t₀)).im = 0 :=
    planar_amplitude_im_eq_zero barbellK4Graph (barbellPath t₀) (barbellPath_planar t₀)
  exact Complex.ext (by simpa [f] using ht₀_re) ht₀_im

/-- **Formal Disproof of Malkoun's Conjecture A** (`arXiv:2508.13472v3`):
there exists a finite connected simple graph (`barbellK4Graph`, $n=8, m=13$) and a point
in $C_G(\mathbb{R}^3)$ where $\mathcal{A}_G(\mathbf{x}) = 0$. -/
theorem disproof_malkoun_conjecture_A :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G, malkounAmplitude G x = 0 := by
  rcases exists_barbellPath_zero with ⟨t₀, _, ht₀⟩
  exact ⟨8, barbellK4Graph, inferInstance, barbellK4Graph_connected, barbellPath t₀, ht₀⟩

/-- **Formal Disproof of Malkoun's Conjecture B** (`arXiv:2508.13472v3`):
$c_G = \inf_{C_G(\mathbb{R}^3)} |\mathcal{A}_G(\mathbf{x})| < 1$ (in fact $= 0$) for connected `barbellK4Graph`. -/
theorem disproof_malkoun_conjecture_B :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G, ‖malkounAmplitude G x‖ < 1 := by
  rcases exists_barbellPath_zero with ⟨t₀, _, ht₀⟩
  exact ⟨8, barbellK4Graph, inferInstance, barbellK4Graph_connected, barbellPath t₀, by
    rw [ht₀, norm_zero]; norm_num⟩

/-- **Formal Disproof of Malkoun's Section 6 Connected-Graph Question** (`arXiv:2508.13472v3`):
for connected `barbellK4Graph` at `barbellPath 1`, $\mathcal{A}_G \in \mathbb{R}$ is strictly negative
(`-1713503232016128 / 30028482030625`). -/
theorem disproof_malkoun_section_6 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ ∃ x : ConfigSpace G,
        (malkounAmplitude G x).re < 0 ∧ (malkounAmplitude G x).im = 0 := by
  refine ⟨8, barbellK4Graph, inferInstance, barbellK4Graph_connected, barbellPath 1, ?_⟩
  rw [malkounAmplitude_barbellPath_one]
  norm_num

end HomotopyDisproof

end Matematyka.MalkounCounterexample
