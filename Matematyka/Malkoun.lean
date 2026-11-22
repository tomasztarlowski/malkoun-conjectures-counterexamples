module

public import Mathlib
/-!
# Malkoun's Graph Generalizations of the Atiyah–Sutcliffe Conjectures

Formal building blocks from Joseph Malkoun,
*Finite graphs and configurations of points* (`arXiv:2508.13472v3`, Sept 7, 2026).
-/

@[expose] public section

namespace Matematyka.Malkoun

/-- Core algebraic identity behind Malkoun Lemma 5.1:
`(1 - ‖α‖^2) * (1 - ‖β‖^2) - ‖γ - α * β‖^2` equals
`1 + 2 * Re(α * β * conj γ) - ‖α‖^2 - ‖β‖^2 - ‖γ‖^2`. -/
lemma norm_sub_mul_identity (α β γ : ℂ) :
    (1 - ‖α‖ ^ 2) * (1 - ‖β‖ ^ 2) - ‖γ - α * β‖ ^ 2 =
      1 + 2 * (α * β * starRingEnd ℂ γ).re - ‖α‖ ^ 2 - ‖β‖ ^ 2 - ‖γ‖ ^ 2 := by
  have hα : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hβ : ‖β‖ ^ 2 = β.re ^ 2 + β.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hγ : ‖γ‖ ^ 2 = γ.re ^ 2 + γ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hsub : ‖γ - α * β‖ ^ 2 = (γ - α * β).re ^ 2 + (γ - α * β).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hα, hβ, hγ, hsub]
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Malkoun Lemma 5.1 (Section 5, arXiv:2508.13472v3):
Nonnegativity of the Hermitian 3×3 determinant condition is equivalent to the
disk bound `‖γ - α * β‖^2 ≤ (1 - ‖α‖^2) * (1 - ‖β‖^2)`. -/
theorem malkoun_lemma_5_1_core (α β γ : ℂ) :
    0 ≤ 1 + 2 * (α * β * starRingEnd ℂ γ).re - ‖α‖ ^ 2 - ‖β‖ ^ 2 - ‖γ‖ ^ 2 ↔
      ‖γ - α * β‖ ^ 2 ≤ (1 - ‖α‖ ^ 2) * (1 - ‖β‖ ^ 2) := by
  have hid := norm_sub_mul_identity α β γ
  constructor <;> intro h <;> linarith

/-- Malkoun Section 5, Case `n = 3` (`LG_3` satisfies Conjecture C):
`Re(1 + h₁₂ * conj h₁₂) ≥ 1`, with equality iff `h₁₂ = 0`. -/
theorem malkoun_lg3_conj_c (h12 : ℂ) :
    1 ≤ (1 + h12 * starRingEnd ℂ h12).re := by
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg h12.re, sq_nonneg h12.im]

theorem malkoun_lg3_conj_c_eq_iff (h12 : ℂ) :
    (1 + h12 * starRingEnd ℂ h12).re = 1 ↔ h12 = 0 := by
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  constructor
  · intro h
    have hre : h12.re = 0 := by nlinarith [sq_nonneg h12.re, sq_nonneg h12.im]
    have him : h12.im = 0 := by nlinarith [sq_nonneg h12.re, sq_nonneg h12.im]
    exact Complex.ext hre him
  · intro h
    subst h
    simp

lemma two_mul_sqrt_am_gm (u v : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    2 * (u * v * Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2))) ≤ u ^ 2 + v ^ 2 - 2 * u ^ 2 * v ^ 2 := by
  have h1u : 0 ≤ 1 - u ^ 2 := by nlinarith
  have h1v : 0 ≤ 1 - v ^ 2 := by nlinarith
  have hsqrt : Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2)) =
      Real.sqrt (1 - u ^ 2) * Real.sqrt (1 - v ^ 2) := Real.sqrt_mul h1u _
  rw [hsqrt]
  have hsq : 0 ≤ (u * Real.sqrt (1 - v ^ 2) - v * Real.sqrt (1 - u ^ 2)) ^ 2 := sq_nonneg _
  have hru : (Real.sqrt (1 - u ^ 2)) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt h1u
  have hrv : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt h1v
  nlinarith

/-- Malkoun Lemma 5.2 (Section 5, arXiv:2508.13472v3):
AM-GM upper bounds for `A`, `B`, `C` in the `LG_5` proof. -/
theorem malkoun_lemma_5_2 (a b c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    let s := Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2))
    let t := Real.sqrt ((1 - b ^ 2) * (1 - c ^ 2))
    let A := a * b * s * (1 + c ^ 2)
    let B := b * c * t * (1 + a ^ 2)
    let C := a * c * s * t
    2 * A ≤ (1 + c ^ 2) * (a ^ 2 + b ^ 2 - 2 * a ^ 2 * b ^ 2) ∧
      2 * B ≤ (1 + a ^ 2) * (b ^ 2 + c ^ 2 - 2 * b ^ 2 * c ^ 2) ∧
      2 * C ≤ (1 - b ^ 2) * (a ^ 2 + c ^ 2 - 2 * a ^ 2 * c ^ 2) := by
  intro s t A B C
  have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
  have h1b : 0 ≤ 1 - b ^ 2 := by nlinarith
  have h1c : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hAB : 2 * A ≤ (1 + c ^ 2) * (a ^ 2 + b ^ 2 - 2 * a ^ 2 * b ^ 2) := by
    have hcore := two_mul_sqrt_am_gm a b ha0 ha1 hb0 hb1
    have hpos : 0 ≤ 1 + c ^ 2 := by positivity
    dsimp [A, s]
    nlinarith
  have hBC : 2 * B ≤ (1 + a ^ 2) * (b ^ 2 + c ^ 2 - 2 * b ^ 2 * c ^ 2) := by
    have hcore := two_mul_sqrt_am_gm b c hb0 hb1 hc0 hc1
    have hpos : 0 ≤ 1 + a ^ 2 := by positivity
    dsimp [B, t]
    nlinarith
  have hst : s * t = (1 - b ^ 2) * Real.sqrt ((1 - a ^ 2) * (1 - c ^ 2)) := by
    dsimp [s, t]
    rw [Real.sqrt_mul h1a, Real.sqrt_mul h1b, Real.sqrt_mul h1a]
    have hsq : Real.sqrt (1 - b ^ 2) * Real.sqrt (1 - b ^ 2) = 1 - b ^ 2 :=
      Real.mul_self_sqrt h1b
    calc
      Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) *
          (Real.sqrt (1 - b ^ 2) * Real.sqrt (1 - c ^ 2))
        = (Real.sqrt (1 - b ^ 2) * Real.sqrt (1 - b ^ 2)) *
            (Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - c ^ 2)) := by ring
      _ = (1 - b ^ 2) * (Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - c ^ 2)) := by rw [hsq]
  have hC : 2 * C ≤ (1 - b ^ 2) * (a ^ 2 + c ^ 2 - 2 * a ^ 2 * c ^ 2) := by
    have hcore := two_mul_sqrt_am_gm a c ha0 ha1 hc0 hc1
    have hmul : 2 * C = (1 - b ^ 2) * (2 * (a * c * Real.sqrt ((1 - a ^ 2) * (1 - c ^ 2)))) := by
      dsimp [C]
      rw [mul_assoc (a * c) s t, hst]
      ring
    rw [hmul]
    nlinarith
  exact ⟨hAB, hBC, hC⟩

end Matematyka.Malkoun
