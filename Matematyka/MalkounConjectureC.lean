import Matematyka.MalkounConjectureD

/-!
# Formal Disproof of Malkoun's Conjecture C (Trees), `MalkounTreeConjectureDProp`, and Conjectures A & B Restricted to Trees

Building on `MalkounBipartite.lean` and `MalkounConjectureD.lean`, this module refutes
Malkoun's fourth and final main conjecture (**Conjecture C**, `arXiv:2508.13472v3`), as well
as the tree-restricted Conjecture D (`MalkounTreeConjectureDProp`) and Conjectures A and B
restricted to finite trees:

1. **Unnormalized Bipartite Spinor Reduction & Hopf-Pythagorean Map:**
   Proves `malkounAmplitude_bipartite_unnorm` (factoring arbitrary positive edge spinor norms `r e`)
   and `hopfVecGI_spinor_ok` mapping Gaussian-integer edge spinors to exact integer 3D edge vectors.
2. **Exact Planar Zero on the Minimal 10-Vertex Cubic Cherry Tree `cherryTree10` ($n=10, m=9$):**
   An explicit planar $120^\circ$ pinwheel configuration `cherryPinwheelConfig` in $z=0$ with pairwise
   distance $\ge 2$ gives $\mathcal{A}_{T_{10}}(\mathbf{x}) = 0$, proving:
   - `malkounAmplitude_cherryPinwheel_eq_zero`
   - `disproof_malkoun_conjecture_C : ¬ MalkounConjectureCProp`
   - `disproof_malkoun_tree_conjecture_A` (a tree $T$ with $\mathbf{x} \in C_T(\mathbb{R}^3)$ and $\mathcal{A}_T(\mathbf{x}) = 0$)
   - `disproof_malkoun_tree_conjecture_B` (a tree $T$ with $\|\mathcal{A}_T(\mathbf{x})\| < 1$)
   - `disproof_malkoun_tree_conjecture_D : ¬ MalkounTreeConjectureDProp`
3. **Strictly Negative Real Part on Malkoun's Linear Path Family $LG_{15}$ (`pathGraph15`, $n=15, m=14$):**
   Using a $2 \times 2$ Gaussian-integer transfer matrix and Hopf 3D coordinates, proves
   `malkounAmplitude_lg15Neg_re_neg : (malkounAmplitude pathGraph15 lg15NegConfig).re < 0`
   (with exact rational $\operatorname{Re} = -40605770611892600000 / 58001564658819600000 \approx -0.700081$)
   and `disproof_malkoun_path_conjecture_C_neg_re`.
-/

namespace Matematyka.MalkounConjectureC

open Complex Classical Matematyka.MalkounCounterexample Matematyka.MalkounBipartite
  Matematyka.MalkounConjectureD

private lemma fin2_eq (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

private lemma sum_bool_ft {R : Type*} [AddCommMonoid R] (g : Bool → R) :
    (∑ b : Bool, g b) = g false + g true := by
  rw [Fintype.sum_bool, add_comm]

private lemma toC_starGI' (z : GI) : GI.toC (starGI z) = starRingEnd ℂ (GI.toC z) := by
  simp only [starGI, GI.toC, map_add, map_mul, Complex.conj_I, map_intCast, Int.cast_neg]
  ring

private lemma toC_sumFinGI' : ∀ (m : ℕ) (f : Fin m → GI),
    GI.toC (sumFinGI m f) = ∑ i : Fin m, GI.toC (f i)
  | 0, _ => by simp [sumFinGI]
  | m + 1, f => by
      simp only [sumFinGI, GI.toC_add, Fin.sum_univ_succ, toC_sumFinGI' m]

/-! ## Part 1: Conjecture C Statement, Unnormalized Bipartite Reduction, and Hopf Map -/

/-- **Malkoun's Conjecture C (`arXiv:2508.13472v3`, Section 4):**
for every finite tree `T` and every non-collision configuration `x : ConfigSpace T`,
$\operatorname{Re}(\mathcal{A}_T(\mathbf{x})) \ge 1$. -/
def MalkounConjectureCProp : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (_ : DecidableRel T.Adj),
    T.IsTree → ∀ x : ConfigSpace T, 1 ≤ (malkounAmplitude T x).re

/-- **Unnormalized Bipartite Spinor Formula:**
if `Φ e : Fin 2 → ℂ` is any unnormalized $+1$-eigenvector of `pauliDot (unitDir x_{e.1} x_{e.2})`
with squared norm `0 < r e = ‖Φ e 0‖^2 + ‖Φ e 1‖^2`, then
$\mathcal{A}_G(\mathbf{x}) = \overline{f_{\sim_1, \sim_2}(Φᴴ Φ)} / \prod_e r_e$. -/
theorem malkounAmplitude_bipartite_unnorm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (part : Fin n → Bool) (hb : IsBipartite G part) (x : ConfigSpace G)
    (Φ : BipEdge G part → Fin 2 → ℂ) (r : BipEdge G part → ℝ)
    (hr_pos : ∀ e, 0 < r e)
    (hnorm : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = r e)
    (hmul : ∀ e, (pauliDot (unitDir (x.1 e.1.1) (x.1 e.1.2))).mulVec (Φ e) = Φ e) :
    malkounAmplitude G x =
      starRingEnd ℂ (∑ σ₁ : bipP1 G part, ∑ σ₂ : bipP2 G part,
        ∏ e : BipEdge G part,
          (starRingEnd ℂ (Φ (σ₁.1 e) 0) * Φ (σ₂.1 e) 0 +
           starRingEnd ℂ (Φ (σ₁.1 e) 1) * Φ (σ₂.1 e) 1)) /
      ((∏ e : BipEdge G part, r e : ℝ) : ℂ) := by
  let sr : BipEdge G part → ℝ := fun e => Real.sqrt (r e)
  have hsr_pos : ∀ e, 0 < sr e := fun e => Real.sqrt_pos.mpr (hr_pos e)
  have hsr_ne : ∀ e, sr e ≠ 0 := fun e => (hsr_pos e).ne'
  have hsr_sq : ∀ e, sr e ^ 2 = r e := fun e => Real.sq_sqrt (hr_pos e).le
  let Φn : BipEdge G part → Fin 2 → ℂ := fun e k => ((sr e : ℝ)⁻¹ : ℂ) * Φ e k
  have hpos_n : ∀ e, IsPosSpinor (unitDir (x.1 e.1.1) (x.1 e.1.2)) (Φn e) := by
    intro e
    refine ⟨?_, ?_⟩
    · have h0 : ‖Φn e 0‖ = (sr e)⁻¹ * ‖Φ e 0‖ := by
        dsimp only [Φn]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hsr_pos e)]
      have h1 : ‖Φn e 1‖ = (sr e)⁻¹ * ‖Φ e 1‖ := by
        dsimp only [Φn]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hsr_pos e)]
      rw [h0, h1]
      have hsr2_ne : sr e ^ 2 ≠ 0 := pow_ne_zero 2 (hsr_ne e)
      calc ((sr e)⁻¹ * ‖Φ e 0‖) ^ 2 + ((sr e)⁻¹ * ‖Φ e 1‖) ^ 2
          = (sr e ^ 2)⁻¹ * (‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2) := by ring
        _ = (sr e ^ 2)⁻¹ * sr e ^ 2 := by rw [hnorm e, hsr_sq e]
        _ = 1 := inv_mul_cancel₀ hsr2_ne
    · have hsmul : Φn e = (((sr e : ℝ)⁻¹ : ℂ)) • Φ e := funext fun _ => rfl
      rw [hsmul, Matrix.mulVec_smul, hmul e]
  have hpos_bip : ∀ e : BipEdge G part, IsPosSpinor (unitDir (x.1 e.1.1) (x.1 e.1.2)) (bipEdgeSpinor x e) :=
    fun e => isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 e.1.1 e.1.2 e.2.1))
  have hcol : ∀ e : BipEdge G part, ∃ c : ℂ, ‖c‖ ^ 2 = 1 ∧ ∀ k, Φ e k = ((sr e : ℝ) : ℂ) * c * bipEdgeSpinor x e k := by
    intro e
    rcases isPosSpinor_collinear (hpos_bip e) (hpos_n e) with ⟨c, _, hc_eq⟩
    refine ⟨c, ?_, ?_⟩
    · have hc_n : ‖Φn e 0‖ ^ 2 + ‖Φn e 1‖ ^ 2 = 1 := (hpos_n e).1
      rw [hc_eq 0, hc_eq 1, norm_mul, norm_mul] at hc_n
      have heq : ‖c‖ ^ 2 * (‖bipEdgeSpinor x e 0‖ ^ 2 + ‖bipEdgeSpinor x e 1‖ ^ 2) = 1 := by
        nlinarith [sq (‖c‖), sq (‖bipEdgeSpinor x e 0‖), sq (‖bipEdgeSpinor x e 1‖)]
      rw [(hpos_bip e).1, mul_one] at heq
      exact heq
    · intro k
      have hk := hc_eq k
      dsimp only [Φn] at hk
      have hsrC : ((sr e : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hsr_ne e)
      calc Φ e k = ((sr e : ℝ) : ℂ) * (((sr e : ℝ)⁻¹ : ℂ) * Φ e k) := by
            rw [← mul_assoc, mul_inv_cancel₀ hsrC, one_mul]
        _ = ((sr e : ℝ) : ℂ) * c * bipEdgeSpinor x e k := by rw [hk]; ring
  choose c hc_norm hc_eq using hcol
  have hc_conj : ∀ e, starRingEnd ℂ (c e) * c e = 1 := fun e => by
    have hm : c e * starRingEnd ℂ (c e) = ((‖c e‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [mul_comm, hc_norm e, Complex.ofReal_one] at hm
    exact hm
  let Φin : BipEdge G part → BipEdge G part → ℂ := fun a b =>
    starRingEnd ℂ (Φ a 0) * Φ b 0 + starRingEnd ℂ (Φ a 1) * Φ b 1
  have hΦin : ∀ a b, Φin a b =
      (((sr a : ℝ) : ℂ) * ((sr b : ℝ) : ℂ)) * (starRingEnd ℂ (c a) * c b) *
        bipGramMatrix G part x a b := by
    intro a b
    simp only [Φin, bipGramMatrix, hc_eq a 0, hc_eq a 1, hc_eq b 0, hc_eq b 1,
      map_mul, Complex.conj_ofReal]
    ring
  let R : ℝ := ∏ e : BipEdge G part, r e
  have hR_pos : 0 < R := Finset.prod_pos fun e _ => hr_pos e
  have hRC_ne : ((R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
  have hsr_prod : (∏ e : BipEdge G part, ((sr e : ℝ) : ℂ)) *
      (∏ e : BipEdge G part, ((sr e : ℝ) : ℂ)) = ((R : ℝ) : ℂ) := by
    rw [← Finset.prod_mul_distrib]
    simp only [← sq, ← Complex.ofReal_pow, hsr_sq, Complex.ofReal_prod, R]
  have hc_prod : (∏ e : BipEdge G part, starRingEnd ℂ (c e)) *
      (∏ e : BipEdge G part, c e) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun e _ => hc_conj e
  have hsum_eq : (∑ σ₁ : bipP1 G part, ∑ σ₂ : bipP2 G part,
      ∏ e : BipEdge G part, Φin (σ₁.1 e) (σ₂.1 e)) =
      ((R : ℝ) : ℂ) * ∑ σ₁ : bipP1 G part, ∑ σ₂ : bipP2 G part,
        ∏ e : BipEdge G part, bipGramMatrix G part x (σ₁.1 e) (σ₂.1 e) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ₂ _ => ?_
    have hprod_id : (∏ e : BipEdge G part, Φin (σ₁.1 e) (σ₂.1 e)) =
        ((∏ e : BipEdge G part, ((sr (σ₁.1 e) : ℝ) : ℂ)) *
          (∏ e : BipEdge G part, ((sr (σ₂.1 e) : ℝ) : ℂ))) *
        ((∏ e : BipEdge G part, starRingEnd ℂ (c (σ₁.1 e))) *
          (∏ e : BipEdge G part, c (σ₂.1 e))) *
        (∏ e : BipEdge G part, bipGramMatrix G part x (σ₁.1 e) (σ₂.1 e)) := by
      simp_rw [hΦin, Finset.prod_mul_distrib]
    rw [hprod_id]
    rw [Equiv.prod_comp σ₁.1 (fun e => ((sr e : ℝ) : ℂ)),
        Equiv.prod_comp σ₂.1 (fun e => ((sr e : ℝ) : ℂ)),
        Equiv.prod_comp σ₁.1 (fun e => starRingEnd ℂ (c e)),
        Equiv.prod_comp σ₂.1 c, hsr_prod, hc_prod, mul_one]
  change malkounAmplitude G x =
      starRingEnd ℂ (∑ σ₁ : bipP1 G part, ∑ σ₂ : bipP2 G part,
        ∏ e : BipEdge G part, Φin (σ₁.1 e) (σ₂.1 e)) / ((R : ℝ) : ℂ)
  rw [hsum_eq, map_mul, Complex.conj_ofReal, malkounAmplitude_bipartite_eq_conj_gram G part hb x]
  exact (mul_div_cancel_left₀ _ hRC_ne).symm

/-- Squared Euclidean norm of a Gaussian-integer edge spinor `s : Fin 2 → GI`. -/
def hopfNormGI (s : Fin 2 → GI) : ℤ :=
  (s 0).re ^ 2 + (s 0).im ^ 2 + (s 1).re ^ 2 + (s 1).im ^ 2

/-- Integer 3D direction vector $\langle s, \vec{\sigma} s \rangle \in \mathbb{Z}^3$
given by the Hopf map for `s : Fin 2 → GI`. -/
def hopfVecGI (s : Fin 2 → GI) : Fin 3 → ℤ
  | 0 => 2 * ((s 0).re * (s 1).re + (s 0).im * (s 1).im)
  | 1 => 2 * ((s 0).re * (s 1).im - (s 0).im * (s 1).re)
  | 2 => (s 0).re ^ 2 + (s 0).im ^ 2 - (s 1).re ^ 2 - (s 1).im ^ 2

lemma hopfVecGI_sq (s : Fin 2 → GI) :
    hopfVecGI s 0 ^ 2 + hopfVecGI s 1 ^ 2 + hopfVecGI s 2 ^ 2 = hopfNormGI s ^ 2 := by
  simp only [hopfVecGI, hopfNormGI]
  ring

lemma hopfVecGI_spinor_ok (s : Fin 2 → GI) (hr : 0 < hopfNormGI s) (pu pv : Fin 3 → ℝ)
    (hdiff : ∀ j : Fin 3, pv j - pu j = (hopfVecGI s j : ℝ)) :
    pu ≠ pv ∧
    ‖GI.toC (s 0)‖ ^ 2 + ‖GI.toC (s 1)‖ ^ 2 = (hopfNormGI s : ℝ) ∧
    (pauliDot (unitDir pu pv)).mulVec (fun k => GI.toC (s k)) = fun k => GI.toC (s k) := by
  have hrR : (0 : ℝ) < (hopfNormGI s : ℝ) := Int.cast_pos.mpr hr
  have hr_ne : (hopfNormGI s : ℝ) ≠ 0 := hrR.ne'
  have hsqR : (pv 0 - pu 0) ^ 2 + (pv 1 - pu 1) ^ 2 + (pv 2 - pu 2) ^ 2 =
      (hopfNormGI s : ℝ) ^ 2 := by
    rw [hdiff 0, hdiff 1, hdiff 2]
    exact_mod_cast hopfVecGI_sq s
  have heuclid : euclidNorm (fun j => pv j - pu j) = (hopfNormGI s : ℝ) := by
    rw [euclidNorm, hsqR, Real.sqrt_sq hrR.le]
  have hne : pu ≠ pv := by
    intro heq
    subst heq
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hsqR
    linarith [pow_pos hrR 2]
  have hnorm_sum : ‖GI.toC (s 0)‖ ^ 2 + ‖GI.toC (s 1)‖ ^ 2 = (hopfNormGI s : ℝ) := by
    have hns : ∀ z : GI, ‖GI.toC z‖ ^ 2 = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := fun z => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [GI.toC]
      ring
    rw [hns (s 0), hns (s 1)]
    simp only [hopfNormGI, Int.cast_add, Int.cast_pow]
    ring
  have hdir : ∀ j : Fin 3, unitDir pu pv j = (hopfVecGI s j : ℝ) / (hopfNormGI s : ℝ) := fun j => by
    simp only [unitDir, heuclid, hdiff j]
  refine ⟨hne, hnorm_sum, funext fun k => ?_⟩
  rcases fin2_eq k with rfl | rfl <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, hdir 0, hdir 1, hdir 2] <;>
    apply Complex.ext <;>
    simp only [GI.toC, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
      Complex.intCast_im, hopfVecGI, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_ofNat] <;>
    (field_simp [hr_ne]; simp only [hopfNormGI, Int.cast_add, Int.cast_pow]; ring)

/-! ## Part 2: Exact Planar Zero on the Minimal 10-Vertex Cubic Cherry Tree `cherryTree10` -/

section CherryTree10

/-- The 10-vertex, 9-edge cubic cherry tree $T_{10}$ (center `0` joined to `1, 4, 7`,
each carrying two leaves `{2,3}`, `{5,6}`, `{8,9}`). -/
def cherryTree10 : SimpleGraph (Fin 10) where
  Adj u v :=
    let a := min u.val v.val
    let b := max u.val v.val
    (a = 0 ∧ (b = 1 ∨ b = 4 ∨ b = 7)) ∨
    (a = 1 ∧ (b = 2 ∨ b = 3)) ∨
    (a = 4 ∧ (b = 5 ∨ b = 6)) ∨
    (a = 7 ∧ (b = 8 ∨ b = 9))
  symm := ⟨fun u v h => by dsimp only at *; rwa [min_comm, max_comm]⟩
  loopless := ⟨fun x h => by dsimp only at h; omega⟩

instance instDecidableRelCherry10 : DecidableRel cherryTree10.Adj := fun u v =>
  inferInstanceAs (Decidable (
    (min u.val v.val = 0 ∧ (max u.val v.val = 1 ∨ max u.val v.val = 4 ∨ max u.val v.val = 7)) ∨
    (min u.val v.val = 1 ∧ (max u.val v.val = 2 ∨ max u.val v.val = 3)) ∨
    (min u.val v.val = 4 ∧ (max u.val v.val = 5 ∨ max u.val v.val = 6)) ∨
    (min u.val v.val = 7 ∧ (max u.val v.val = 8 ∨ max u.val v.val = 9))))

theorem cherryTree10_connected : cherryTree10.Connected := by
  have hr : ∀ u : Fin 10, cherryTree10.Reachable 0 u := fun u => by
    fin_cases u
    · exact SimpleGraph.Reachable.refl 0
    · exact SimpleGraph.Adj.reachable (by decide)
    · exact (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 0 1)).trans
        (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 1 2))
    · exact (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 0 1)).trans
        (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 1 3))
    · exact SimpleGraph.Adj.reachable (by decide)
    · exact (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 0 4)).trans
        (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 4 5))
    · exact (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 0 4)).trans
        (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 4 6))
    · exact SimpleGraph.Adj.reachable (by decide)
    · exact (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 0 7)).trans
        (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 7 8))
    · exact (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 0 7)).trans
        (SimpleGraph.Adj.reachable (by decide : cherryTree10.Adj 7 9))
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

theorem cherryTree10_isTree : cherryTree10.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨cherryTree10_connected, ?_⟩
  rw [Nat.card_coe_set_eq, ← SimpleGraph.coe_edgeFinset cherryTree10, Set.ncard_coe_finset,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

def cherryPart (u : Fin 10) : Bool := decide (u = 1 ∨ u = 4 ∨ u = 7)

lemma cherryTree10_isBipartite : IsBipartite cherryTree10 cherryPart := by
  intro u v huv; revert u v huv; decide

private def cherryEdges : Fin 9 → BipEdge cherryTree10 cherryPart
  | 0 => ⟨(0, 1), by decide⟩
  | 1 => ⟨(2, 1), by decide⟩
  | 2 => ⟨(3, 1), by decide⟩
  | 3 => ⟨(0, 4), by decide⟩
  | 4 => ⟨(5, 4), by decide⟩
  | 5 => ⟨(6, 4), by decide⟩
  | 6 => ⟨(0, 7), by decide⟩
  | 7 => ⟨(8, 7), by decide⟩
  | 8 => ⟨(9, 7), by decide⟩

private lemma cherry_bipEdge_cases (e : BipEdge cherryTree10 cherryPart) :
    e = cherryEdges 0 ∨ e = cherryEdges 1 ∨ e = cherryEdges 2 ∨
    e = cherryEdges 3 ∨ e = cherryEdges 4 ∨ e = cherryEdges 5 ∨
    e = cherryEdges 6 ∨ e = cherryEdges 7 ∨ e = cherryEdges 8 := by
  rcases e with ⟨⟨u, v⟩, hadj, hu, hv⟩
  have h :
      (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 1) ∨ (u = 3 ∧ v = 1) ∨
      (u = 0 ∧ v = 4) ∨ (u = 5 ∧ v = 4) ∨ (u = 6 ∧ v = 4) ∨
      (u = 0 ∧ v = 7) ∨ (u = 8 ∧ v = 7) ∨ (u = 9 ∧ v = 7) := by
    revert u v hadj hu hv; decide
  rcases h with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [cherryEdges]

private def cherryEdgeEquiv : Fin 9 ≃ BipEdge cherryTree10 cherryPart where
  toFun := cherryEdges
  invFun e :=
    if e.1.2 = 1 then (if e.1.1 = 0 then 0 else if e.1.1 = 2 then 1 else 2)
    else if e.1.2 = 4 then (if e.1.1 = 0 then 3 else if e.1.1 = 5 then 4 else 5)
    else (if e.1.1 = 0 then 6 else if e.1.1 = 8 then 7 else 8)
  left_inv i := by fin_cases i <;> rfl
  right_inv e := by
    rcases cherry_bipEdge_cases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def fin3PermCycFun : Fin 6 → Equiv.Perm (Fin 3)
  | 0 => 1
  | 1 => Equiv.swap 0 1
  | 2 => Equiv.swap 1 2
  | 3 => Equiv.swap 0 2
  | 4 => Equiv.swap 0 1 * Equiv.swap 1 2
  | 5 => Equiv.swap 1 2 * Equiv.swap 0 1

private def fin3PermCycEquiv : Fin 6 ≃ Equiv.Perm (Fin 3) where
  toFun := fin3PermCycFun
  invFun σ :=
    if σ 0 = 0 then (if σ 1 = 1 then 0 else 2)
    else if σ 0 = 1 then (if σ 1 = 0 then 1 else 4)
    else (if σ 1 = 1 then 3 else 5)
  left_inv i := by fin_cases i <;> decide
  right_inv σ := by
    apply Equiv.ext; intro x; dsimp only
    have hc3 : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := fun a => by fin_cases a <;> simp
    have h01 : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
    have h02 : σ 0 ≠ σ 2 := fun h => absurd (σ.injective h) (by decide)
    have h12 : σ 1 ≠ σ 2 := fun h => absurd (σ.injective h) (by decide)
    rcases hc3 (σ 0) with h0 | h0 | h0 <;> rcases hc3 (σ 1) with h1 | h1 | h1 <;>
      rcases hc3 (σ 2) with h2 | h2 | h2
    all_goals first
      | (exfalso; exact h01 (h0.trans h1.symm))
      | (exfalso; exact h02 (h0.trans h2.symm))
      | (exfalso; exact h12 (h1.trans h2.symm))
      | ((rcases hc3 x with rfl | rfl | rfl) <;>
          rw [h0] <;> rw [h1] <;> (try rw [h2]) <;> decide)

private lemma fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a <;> simp

private def cherryHubPermFun (π : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 9) where
  toFun i :=
    if i = 0 then ![0, 3, 6] (π 0)
    else if i = 3 then ![0, 3, 6] (π 1)
    else if i = 6 then ![0, 3, 6] (π 2)
    else i
  invFun i :=
    if i = 0 then ![0, 3, 6] (π.symm 0)
    else if i = 3 then ![0, 3, 6] (π.symm 1)
    else if i = 6 then ![0, 3, 6] (π.symm 2)
    else i
  left_inv i := by
    fin_cases i <;> dsimp only
    · have hs : π.symm (π 0) = 0 := π.symm_apply_apply 0
      rcases fin3_cases (π 0) with h | h | h <;> simp [h] at hs ⊢ <;> simp [hs]
    · rfl
    · rfl
    · have hs : π.symm (π 1) = 1 := π.symm_apply_apply 1
      rcases fin3_cases (π 1) with h | h | h <;> simp [h] at hs ⊢ <;> simp [hs]
    · rfl
    · rfl
    · have hs : π.symm (π 2) = 2 := π.symm_apply_apply 2
      rcases fin3_cases (π 2) with h | h | h <;> simp [h] at hs ⊢ <;> simp [hs]
    · rfl
    · rfl
  right_inv i := by
    fin_cases i <;> dsimp only
    · have ha : π (π.symm 0) = 0 := π.apply_symm_apply 0
      rcases fin3_cases (π.symm 0) with h | h | h <;> simp [h] at ha ⊢ <;> simp [ha]
    · rfl
    · rfl
    · have ha : π (π.symm 1) = 1 := π.apply_symm_apply 1
      rcases fin3_cases (π.symm 1) with h | h | h <;> simp [h] at ha ⊢ <;> simp [ha]
    · rfl
    · rfl
    · have ha : π (π.symm 2) = 2 := π.apply_symm_apply 2
      rcases fin3_cases (π.symm 2) with h | h | h <;> simp [h] at ha ⊢ <;> simp [ha]
    · rfl
    · rfl

private lemma cherry_fst_hub (u v : Fin 10)
    (h : cherryTree10.Adj u v ∧ cherryPart u = false ∧ cherryPart v = true) (hu : u = 0) :
    cherryEdgeEquiv.symm ⟨(u, v), h⟩ = 0 ∨ cherryEdgeEquiv.symm ⟨(u, v), h⟩ = 3 ∨
      cherryEdgeEquiv.symm ⟨(u, v), h⟩ = 6 := by
  revert u v h hu; decide

private lemma cherry_fst_leaf_fix (i : Fin 9) (hi0 : i ≠ 0) (hi3 : i ≠ 3) (hi6 : i ≠ 6)
    (u v : Fin 10) (h : cherryTree10.Adj u v ∧ cherryPart u = false ∧ cherryPart v = true)
    (hu : u = (cherryEdges i).1.1) :
    cherryEdgeEquiv.symm ⟨(u, v), h⟩ = i := by
  revert i hi0 hi3 hi6 u v h hu; decide

private lemma cherry_hub_fst (a : Fin 3) : (cherryEdges (![0, 3, 6] a)).1.1 = 0 := by
  fin_cases a <;> rfl

private def cherryHubIdx : Fin 9 → Fin 3
  | 0 => 0 | 3 => 1 | 6 => 2 | _ => 2

private lemma cherryHubIdx_hub (a : Fin 3) : cherryHubIdx (![0, 3, 6] a) = a := by
  fin_cases a <;> rfl

private lemma cherryHubPermFun_hub (π : Equiv.Perm (Fin 3)) (c : Fin 3) :
    cherryHubPermFun π (![0, 3, 6] c) = ![0, 3, 6] (π c) := by
  fin_cases c <;> simp [cherryHubPermFun]

private def cherryP1Inv (σ : bipP1 cherryTree10 cherryPart) : Equiv.Perm (Fin 3) :=
  let σ' := Equiv.permCongr cherryEdgeEquiv.symm σ.1
  have himg : ∀ c : Fin 3, σ' (![0, 3, 6] c) = 0 ∨ σ' (![0, 3, 6] c) = 3 ∨ σ' (![0, 3, 6] c) = 6 := by
    intro c
    rcases hσc : σ.1 (cherryEdges (![0, 3, 6] c)) with ⟨⟨u, v⟩, h⟩
    have hu : u = 0 := by
      have hp := σ.2 (cherryEdges (![0, 3, 6] c))
      rw [hσc] at hp
      exact hp.trans (cherry_hub_fst c)
    change cherryEdgeEquiv.symm (σ.1 (cherryEdges (![0, 3, 6] c))) = 0 ∨
      cherryEdgeEquiv.symm (σ.1 (cherryEdges (![0, 3, 6] c))) = 3 ∨
      cherryEdgeEquiv.symm (σ.1 (cherryEdges (![0, 3, 6] c))) = 6
    rw [hσc]
    exact cherry_fst_hub u v h hu
  have himg_sym : ∀ c : Fin 3, σ'.symm (![0, 3, 6] c) = 0 ∨ σ'.symm (![0, 3, 6] c) = 3 ∨ σ'.symm (![0, 3, 6] c) = 6 := by
    intro c
    rcases hσc : σ.1⁻¹ (cherryEdges (![0, 3, 6] c)) with ⟨⟨u, v⟩, h⟩
    have hu : u = 0 := by
      have hp := ((bipP1 cherryTree10 cherryPart).inv_mem σ.2) (cherryEdges (![0, 3, 6] c))
      rw [hσc] at hp
      exact hp.trans (cherry_hub_fst c)
    have hsym : σ'.symm (![0, 3, 6] c) =
        cherryEdgeEquiv.symm (σ.1⁻¹ (cherryEdges (![0, 3, 6] c))) := by
      rw [Equiv.symm_apply_eq]
      dsimp only [σ', Equiv.permCongr_apply]
      simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
      change _ = cherryEdgeEquiv.symm (σ.1 (σ.1.symm (cherryEdgeEquiv _)))
      rw [σ.1.apply_symm_apply, Equiv.symm_apply_apply]
    rw [hsym, hσc]
    exact cherry_fst_hub u v h hu
  { toFun := fun c => cherryHubIdx (σ' (![0, 3, 6] c))
    invFun := fun c => cherryHubIdx (σ'.symm (![0, 3, 6] c))
    left_inv := fun c => by
      dsimp only
      have hs : ![0, 3, 6] (cherryHubIdx (σ' (![0, 3, 6] c))) = σ' (![0, 3, 6] c) := by
        rcases himg c with h | h | h <;> simp [cherryHubIdx, h]
      rw [hs, Equiv.symm_apply_apply]
      fin_cases c <;> rfl
    right_inv := fun c => by
      dsimp only
      have hs : ![0, 3, 6] (cherryHubIdx (σ'.symm (![0, 3, 6] c))) = σ'.symm (![0, 3, 6] c) := by
        rcases himg_sym c with h | h | h <;> simp [cherryHubIdx, h]
      rw [hs, Equiv.apply_symm_apply]
      fin_cases c <;> rfl }

private lemma cherry_hub_idx_inv (x : Fin 9) (hx : x = 0 ∨ x = 3 ∨ x = 6) :
    (![0, 3, 6] : Fin 3 → Fin 9) (cherryHubIdx x) = x := by
  rcases hx with rfl | rfl | rfl <;> rfl

private def cherryP1Equiv : Equiv.Perm (Fin 3) ≃ bipP1 cherryTree10 cherryPart where
  toFun π := ⟨Equiv.permCongr cherryEdgeEquiv (cherryHubPermFun π), fun e => by
    obtain ⟨i, rfl⟩ := cherryEdgeEquiv.surjective e
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change (cherryEdges (cherryHubPermFun π i)).1.1 = (cherryEdges i).1.1
    dsimp only [cherryHubPermFun, Equiv.coe_fn_mk]
    fin_cases i
    · exact (cherry_hub_fst (π 0)).trans rfl
    · rfl
    · rfl
    · exact (cherry_hub_fst (π 1)).trans rfl
    · rfl
    · rfl
    · exact (cherry_hub_fst (π 2)).trans rfl
    · rfl
    · rfl⟩
  invFun := cherryP1Inv
  left_inv π := by
    apply Equiv.ext; intro c
    dsimp only [cherryP1Inv, Equiv.coe_fn_mk, Equiv.permCongr_apply]
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply]
    dsimp only [Equiv.coe_fn_mk]
    rw [cherryHubPermFun_hub, cherryHubIdx_hub]
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    obtain ⟨i, rfl⟩ := cherryEdgeEquiv.surjective e
    let σ' := Equiv.permCongr cherryEdgeEquiv.symm σ.1
    have hfix : ∀ k : Fin 9, k ≠ 0 → k ≠ 3 → k ≠ 6 → σ' k = k := by
      intro k hk0 hk3 hk6
      rcases hσk : σ.1 (cherryEdges k) with ⟨⟨u, v⟩, h⟩
      have hu : u = (cherryEdges k).1.1 := by
        have hp := σ.2 (cherryEdges k)
        rw [hσk] at hp
        exact hp
      change cherryEdgeEquiv.symm (σ.1 (cherryEdges k)) = k
      rw [hσk]
      exact cherry_fst_leaf_fix k hk0 hk3 hk6 u v h hu
    have h036 : ∀ c : Fin 3, σ' (![0, 3, 6] c) = 0 ∨ σ' (![0, 3, 6] c) = 3 ∨ σ' (![0, 3, 6] c) = 6 := by
      intro c
      rcases hσc : σ.1 (cherryEdges (![0, 3, 6] c)) with ⟨⟨u, v⟩, h⟩
      have hu : u = 0 := by
        have hp := σ.2 (cherryEdges (![0, 3, 6] c))
        rw [hσc] at hp
        exact hp.trans (cherry_hub_fst c)
      change cherryEdgeEquiv.symm (σ.1 (cherryEdges (![0, 3, 6] c))) = 0 ∨
        cherryEdgeEquiv.symm (σ.1 (cherryEdges (![0, 3, 6] c))) = 3 ∨
        cherryEdgeEquiv.symm (σ.1 (cherryEdges (![0, 3, 6] c))) = 6
      rw [hσc]
      exact cherry_fst_hub u v h hu
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change cherryEdges (cherryHubPermFun (cherryP1Inv σ) i) = σ.1 (cherryEdges i)
    fin_cases i
    · change cherryEdges (![0, 3, 6] (cherryHubIdx (σ' 0))) = σ.1 (cherryEdges 0)
      rw [cherry_hub_idx_inv (σ' 0) (h036 0)]
      exact cherryEdgeEquiv.apply_symm_apply _
    · have h1 := hfix 1 (by decide) (by decide) (by decide)
      change cherryEdges 1 = σ.1 (cherryEdges 1)
      conv_lhs => rw [← h1]
      exact cherryEdgeEquiv.apply_symm_apply _
    · have h2 := hfix 2 (by decide) (by decide) (by decide)
      change cherryEdges 2 = σ.1 (cherryEdges 2)
      conv_lhs => rw [← h2]
      exact cherryEdgeEquiv.apply_symm_apply _
    · change cherryEdges (![0, 3, 6] (cherryHubIdx (σ' 3))) = σ.1 (cherryEdges 3)
      rw [cherry_hub_idx_inv (σ' 3) (h036 1)]
      exact cherryEdgeEquiv.apply_symm_apply _
    · have h4 := hfix 4 (by decide) (by decide) (by decide)
      change cherryEdges 4 = σ.1 (cherryEdges 4)
      conv_lhs => rw [← h4]
      exact cherryEdgeEquiv.apply_symm_apply _
    · have h5 := hfix 5 (by decide) (by decide) (by decide)
      change cherryEdges 5 = σ.1 (cherryEdges 5)
      conv_lhs => rw [← h5]
      exact cherryEdgeEquiv.apply_symm_apply _
    · change cherryEdges (![0, 3, 6] (cherryHubIdx (σ' 6))) = σ.1 (cherryEdges 6)
      rw [cherry_hub_idx_inv (σ' 6) (h036 2)]
      exact cherryEdgeEquiv.apply_symm_apply _
    · have h7 := hfix 7 (by decide) (by decide) (by decide)
      change cherryEdges 7 = σ.1 (cherryEdges 7)
      conv_lhs => rw [← h7]
      exact cherryEdgeEquiv.apply_symm_apply _
    · have h8 := hfix 8 (by decide) (by decide) (by decide)
      change cherryEdges 8 = σ.1 (cherryEdges 8)
      conv_lhs => rw [← h8]
      exact cherryEdgeEquiv.apply_symm_apply _

private def cherryBlockPermFun (τ : Fin 3 → Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 9) where
  toFun i :=
    if h3 : i.val < 3 then ⟨(τ 0 ⟨i.val, h3⟩).val, by omega⟩
    else if h6 : i.val < 6 then ⟨3 + (τ 1 ⟨i.val - 3, by omega⟩).val, by omega⟩
    else ⟨6 + (τ 2 ⟨i.val - 6, by omega⟩).val, by omega⟩
  invFun i :=
    if h3 : i.val < 3 then ⟨((τ 0).symm ⟨i.val, h3⟩).val, by omega⟩
    else if h6 : i.val < 6 then ⟨3 + ((τ 1).symm ⟨i.val - 3, by omega⟩).val, by omega⟩
    else ⟨6 + ((τ 2).symm ⟨i.val - 6, by omega⟩).val, by omega⟩
  left_inv i := by
    rcases i with ⟨iv, hiv⟩
    apply Fin.ext
    by_cases h3 : iv < 3
    · have hlt := (τ 0 ⟨iv, h3⟩).isLt
      simp [h3, hlt]
    · by_cases h6 : iv < 6
      · have hlt := (τ 1 ⟨iv - 3, by omega⟩).isLt
        have hnot3 : ¬ 3 + (τ 1 ⟨iv - 3, by omega⟩).val < 3 := by omega
        have hlt6 : 3 + (τ 1 ⟨iv - 3, by omega⟩).val < 6 := by omega
        simp [h3, h6, hnot3, hlt6]
        omega
      · have hlt := (τ 2 ⟨iv - 6, by omega⟩).isLt
        have hnot3 : ¬ 6 + (τ 2 ⟨iv - 6, by omega⟩).val < 3 := by omega
        have hnot6 : ¬ 6 + (τ 2 ⟨iv - 6, by omega⟩).val < 6 := by omega
        simp [h3, h6, hnot3, hnot6]
        omega
  right_inv i := by
    rcases i with ⟨iv, hiv⟩
    apply Fin.ext
    by_cases h3 : iv < 3
    · have hlt := ((τ 0).symm ⟨iv, h3⟩).isLt
      simp [h3, hlt]
    · by_cases h6 : iv < 6
      · have hlt := ((τ 1).symm ⟨iv - 3, by omega⟩).isLt
        have hnot3 : ¬ 3 + ((τ 1).symm ⟨iv - 3, by omega⟩).val < 3 := by omega
        have hlt6 : 3 + ((τ 1).symm ⟨iv - 3, by omega⟩).val < 6 := by omega
        simp [h3, h6, hnot3, hlt6]
        omega
      · have hlt := ((τ 2).symm ⟨iv - 6, by omega⟩).isLt
        have hnot3 : ¬ 6 + ((τ 2).symm ⟨iv - 6, by omega⟩).val < 3 := by omega
        have hnot6 : ¬ 6 + ((τ 2).symm ⟨iv - 6, by omega⟩).val < 6 := by omega
        simp [h3, h6, hnot3, hnot6]
        omega

private lemma cherryEdges_snd_eq_of_div3 (a b : Fin 9) (h : a.val / 3 = b.val / 3) :
    (cherryEdges a).1.2 = (cherryEdges b).1.2 := by
  revert a b h; decide

private lemma cherry_snd_div3 (c j : Fin 3) (u v : Fin 10)
    (h : cherryTree10.Adj u v ∧ cherryPart u = false ∧ cherryPart v = true)
    (hv : v = (cherryEdges ⟨3 * c.val + j.val, by omega⟩).1.2) :
    (cherryEdgeEquiv.symm ⟨(u, v), h⟩).val / 3 = c.val := by
  revert c j u v h hv; decide

private lemma cherryP2_hblk (σ : bipP2 cherryTree10 cherryPart) (c j : Fin 3) :
    (Equiv.permCongr cherryEdgeEquiv.symm σ.1 ⟨3 * c.val + j.val, by omega⟩).val / 3 = c.val := by
  rcases hσk : σ.1 (cherryEdges ⟨3 * c.val + j.val, by omega⟩) with ⟨⟨u, v⟩, h⟩
  have hv : v = (cherryEdges ⟨3 * c.val + j.val, by omega⟩).1.2 := by
    have hp := σ.2 (cherryEdges ⟨3 * c.val + j.val, by omega⟩)
    rw [hσk] at hp
    exact hp
  change (cherryEdgeEquiv.symm (σ.1 (cherryEdges ⟨3 * c.val + j.val, by omega⟩))).val / 3 = c.val
  rw [hσk]
  exact cherry_snd_div3 c j u v h hv

private def cherryP2Inv (σ : bipP2 cherryTree10 cherryPart) : Fin 3 → Equiv.Perm (Fin 3) :=
  let σ' := Equiv.permCongr cherryEdgeEquiv.symm σ.1
  have hblk : ∀ (c j : Fin 3), (σ' ⟨3 * c.val + j.val, by omega⟩).val / 3 = c.val :=
    cherryP2_hblk σ
  have hblk_sym : ∀ (c j : Fin 3), (σ'.symm ⟨3 * c.val + j.val, by omega⟩).val / 3 = c.val := by
    intro c j
    have hsym : σ'.symm ⟨3 * c.val + j.val, by omega⟩ =
        Equiv.permCongr cherryEdgeEquiv.symm σ.1⁻¹ ⟨3 * c.val + j.val, by omega⟩ := by
      rw [Equiv.symm_apply_eq]
      dsimp only [σ', Equiv.permCongr_apply]
      simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
      change _ = cherryEdgeEquiv.symm (σ.1 (σ.1.symm (cherryEdgeEquiv _)))
      rw [σ.1.apply_symm_apply, Equiv.symm_apply_apply]
    rw [hsym]
    exact cherryP2_hblk ⟨σ.1⁻¹, (bipP2 cherryTree10 cherryPart).inv_mem σ.2⟩ c j
  fun c =>
    { toFun := fun j => ⟨(σ' ⟨3 * c.val + j.val, by omega⟩).val % 3, by omega⟩
      invFun := fun j => ⟨(σ'.symm ⟨3 * c.val + j.val, by omega⟩).val % 3, by omega⟩
      left_inv := fun j => by
        apply Fin.ext; dsimp only
        have hb := hblk c j
        have heq : (⟨3 * c.val + (σ' ⟨3 * c.val + j.val, by omega⟩).val % 3, by omega⟩ : Fin 9) =
            σ' ⟨3 * c.val + j.val, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [heq, Equiv.symm_apply_apply]; dsimp only; omega
      right_inv := fun j => by
        apply Fin.ext; dsimp only
        have hb := hblk_sym c j
        have heq : (⟨3 * c.val + (σ'.symm ⟨3 * c.val + j.val, by omega⟩).val % 3, by omega⟩ : Fin 9) =
            σ'.symm ⟨3 * c.val + j.val, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [heq, Equiv.apply_symm_apply]; dsimp only; omega }

private lemma cherryP2Inv_apply (σ : bipP2 cherryTree10 cherryPart) (c j : Fin 3) :
    cherryP2Inv σ c j =
      ⟨((Equiv.permCongr cherryEdgeEquiv.symm σ.1) ⟨3 * c.val + j.val, by omega⟩).val % 3,
        by omega⟩ := rfl

private def cherryP2Equiv : (Fin 3 → Equiv.Perm (Fin 3)) ≃ bipP2 cherryTree10 cherryPart where
  toFun τ := ⟨Equiv.permCongr cherryEdgeEquiv (cherryBlockPermFun τ), fun e => by
    obtain ⟨k, rfl⟩ := cherryEdgeEquiv.surjective e
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply cherryEdges_snd_eq_of_div3
    dsimp only [cherryBlockPermFun, Equiv.coe_fn_mk]
    by_cases h3 : k.val < 3
    · have hlt := (τ 0 ⟨k.val, h3⟩).isLt
      simp only [h3, ↓reduceDIte]
      change (τ 0 ⟨k.val, h3⟩).val / 3 = k.val / 3
      omega
    · by_cases h6 : k.val < 6
      · have hlt := (τ 1 ⟨k.val - 3, by omega⟩).isLt
        simp only [h3, ↓reduceDIte, h6]
        change (3 + (τ 1 ⟨k.val - 3, by omega⟩).val) / 3 = k.val / 3
        omega
      · have hlt := (τ 2 ⟨k.val - 6, by omega⟩).isLt
        simp only [h3, ↓reduceDIte, h6]
        change (6 + (τ 2 ⟨k.val - 6, by omega⟩).val) / 3 = k.val / 3
        omega⟩
  invFun := cherryP2Inv
  left_inv τ := by
    funext c; ext j
    rw [cherryP2Inv_apply]
    dsimp only
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    dsimp only [cherryBlockPermFun, Equiv.coe_fn_mk]
    have hc0 : (0 : Fin 3).val = 0 := rfl
    have hc1 : (1 : Fin 3).val = 1 := rfl
    have hc2 : (2 : Fin 3).val = 2 := rfl
    rcases fin3_cases c with rfl | rfl | rfl
    · have h3 : 3 * (0 : Fin 3).val + j.val < 3 := by omega
      simp only [h3, ↓reduceDIte]
      have hsub : (⟨3 * (0 : Fin 3).val + j.val, h3⟩ : Fin 3) = j := Fin.ext (by dsimp only; omega)
      rw [hsub]
      exact Nat.mod_eq_of_lt (τ 0 j).isLt
    · have hn3 : ¬ (3 * (1 : Fin 3).val + j.val < 3) := by omega
      have h6 : 3 * (1 : Fin 3).val + j.val < 6 := by omega
      simp only [hn3, ↓reduceDIte, h6]
      have hsub : (⟨3 * (1 : Fin 3).val + j.val - 3, by omega⟩ : Fin 3) = j := Fin.ext (by dsimp only; omega)
      rw [hsub]
      have hlt := (τ 1 j).isLt
      omega
    · have hn3 : ¬ (3 * (2 : Fin 3).val + j.val < 3) := by omega
      have hn6 : ¬ (3 * (2 : Fin 3).val + j.val < 6) := by omega
      simp only [hn3, ↓reduceDIte, hn6]
      have hsub : (⟨3 * (2 : Fin 3).val + j.val - 6, by omega⟩ : Fin 3) = j := Fin.ext (by dsimp only; omega)
      rw [hsub]
      have hlt := (τ 2 j).isLt
      omega
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    obtain ⟨k, rfl⟩ := cherryEdgeEquiv.surjective e
    let σ' := Equiv.permCongr cherryEdgeEquiv.symm σ.1
    have hblk : ∀ (c j : Fin 3), (σ' ⟨3 * c.val + j.val, by omega⟩).val / 3 = c.val :=
      cherryP2_hblk σ
    dsimp only [Equiv.permCongr_apply]
    rw [Equiv.symm_apply_apply]
    change cherryEdges (cherryBlockPermFun (cherryP2Inv σ) k) = σ.1 (cherryEdges k)
    suffices hsuff : cherryBlockPermFun (cherryP2Inv σ) k = σ' k by
      rw [hsuff]
      dsimp only [σ', Equiv.permCongr_apply]
      simp only [Equiv.symm_symm]
      exact cherryEdgeEquiv.apply_symm_apply _
    rcases k with ⟨kv, hkv⟩
    dsimp only [cherryBlockPermFun, cherryP2Inv, Equiv.coe_fn_mk]
    by_cases h3 : kv < 3
    · have hb := hblk 0 ⟨kv, h3⟩
      simp only [h3, ↓reduceDIte]
      apply Fin.ext; dsimp only
      have heq : (⟨3 * (0 : Fin 3).val + (⟨kv, h3⟩ : Fin 3).val, by omega⟩ : Fin 9) = ⟨kv, hkv⟩ :=
        Fin.ext (by dsimp only; omega)
      change (σ' ⟨3 * (0 : Fin 3).val + (⟨kv, h3⟩ : Fin 3).val, by omega⟩).val % 3 =
        (σ' ⟨kv, hkv⟩).val
      rw [heq] at hb ⊢
      omega
    · by_cases h6 : kv < 6
      · have hb := hblk 1 ⟨kv - 3, by omega⟩
        simp only [h3, ↓reduceDIte, h6]
        apply Fin.ext; dsimp only
        have heq : (⟨3 * (1 : Fin 3).val + (⟨kv - 3, by omega⟩ : Fin 3).val, by omega⟩ : Fin 9) =
            ⟨kv, hkv⟩ := Fin.ext (by dsimp only; omega)
        change 3 + (σ' ⟨3 * (1 : Fin 3).val + (⟨kv - 3, by omega⟩ : Fin 3).val, by omega⟩).val % 3 =
          (σ' ⟨kv, hkv⟩).val
        rw [heq] at hb ⊢
        omega
      · have hb := hblk 2 ⟨kv - 6, by omega⟩
        simp only [h3, ↓reduceDIte, h6]
        apply Fin.ext; dsimp only
        have heq : (⟨3 * (2 : Fin 3).val + (⟨kv - 6, by omega⟩ : Fin 3).val, by omega⟩ : Fin 9) =
            ⟨kv, hkv⟩ := Fin.ext (by dsimp only; omega)
        change 6 + (σ' ⟨3 * (2 : Fin 3).val + (⟨kv - 6, by omega⟩ : Fin 3).val, by omega⟩).val % 3 =
          (σ' ⟨kv, hkv⟩).val
        rw [heq] at hb ⊢
        omega

/-- Integer lattice coordinates `(a, b)` for the $120^\circ$ planar pinwheel `(a, b√3, 0)` on `cherryTree10`. -/
def cherryIntA : Fin 10 → ℤ
  | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => -1 | 5 => 0 | 6 => 1 | 7 => -1 | 8 => -3 | 9 => -5

def cherryIntB : Fin 10 → ℤ
  | 0 => 0 | 1 => 0 | 2 => -1 | 3 => -2 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => -1 | 8 => -1 | 9 => -1

/-- Planar pinwheel coordinates in $\mathbb{R}^3$ ($z = 0$) for `cherryTree10`. -/
noncomputable def cherryPinwheelPts (u : Fin 10) : Fin 3 → ℝ
  | 0 => (cherryIntA u : ℝ)
  | 1 => (cherryIntB u : ℝ) * Real.sqrt 3
  | 2 => 0

theorem cherryPinwheelPts_injective : Function.Injective cherryPinwheelPts := by
  intro u v h
  have h0 : (cherryIntA u : ℝ) = (cherryIntA v : ℝ) := congrFun h 0
  have h1 : (cherryIntB u : ℝ) * Real.sqrt 3 = (cherryIntB v : ℝ) * Real.sqrt 3 := congrFun h 1
  have ha : cherryIntA u = cherryIntA v := Int.cast_injective h0
  have hs3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hb : cherryIntB u = cherryIntB v := Int.cast_injective (mul_right_cancel₀ hs3 h1)
  fin_cases u <;> fin_cases v <;> first | rfl | exact absurd ha (by decide) | exact absurd hb (by decide)

/-- Non-collision planar configuration on `cherryTree10`. -/
noncomputable def cherryPinwheelConfig : ConfigSpace cherryTree10 :=
  ⟨cherryPinwheelPts, fun _ _ hadj h =>
    cherryTree10.ne_of_adj hadj (cherryPinwheelPts_injective h)⟩

lemma cherryPinwheel_planar (u : Fin 10) : cherryPinwheelConfig.1 u 2 = 0 := rfl

private noncomputable def omega3 : ℂ :=
  -1 / 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) * Complex.I

private noncomputable def pinDir : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 0
  | 1, 0 => -1 / 2 | 1, 1 => Real.sqrt 3 / 2 | 1, 2 => 0
  | 2, 0 => -1 / 2 | 2, 1 => -(Real.sqrt 3 / 2) | 2, 2 => 0

private noncomputable def pinSpinor : Fin 3 → Fin 2 → ℂ
  | 0, 0 => 1 | 0, 1 => 1
  | 1, 0 => 1 | 1, 1 => omega3
  | 2, 0 => 1 | 2, 1 => starRingEnd ℂ omega3

private def cherryPinClass : Fin 9 → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 1
  | 3 => 1 | 4 => 2 | 5 => 2
  | 6 => 2 | 7 => 0 | 8 => 0

private lemma pinSpinor_norm_sq (a : Fin 3) :
    ‖pinSpinor a 0‖ ^ 2 + ‖pinSpinor a 1‖ ^ 2 = 2 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn1 : ‖omega3‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [omega3, Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.div_ofNat_im, Complex.neg_im, Complex.one_im, Complex.mul_im]
    nlinarith [hs3]
  fin_cases a
  · simp [pinSpinor]; norm_num
  · simp [pinSpinor, hn1]; norm_num
  · simp [pinSpinor, hn1]; norm_num

private lemma pinSpinor_pauli (a : Fin 3) :
    (pauliDot (pinDir a)).mulVec (pinSpinor a) = pinSpinor a := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  funext k
  fin_cases a <;> rcases fin2_eq k with rfl | rfl <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, pinDir, pinSpinor,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, omega3] <;>
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im] <;>
    nlinarith [hs3]

private def cherryDA (i : Fin 9) : ℤ :=
  cherryIntA (cherryEdges i).1.2 - cherryIntA (cherryEdges i).1.1

private def cherryDB (i : Fin 9) : ℤ :=
  cherryIntB (cherryEdges i).1.2 - cherryIntB (cherryEdges i).1.1

private def cherryStepLen : Fin 9 → ℤ
  | 0 => 2 | 1 => 2 | 2 => 4
  | 3 => 2 | 4 => 2 | 5 => 4
  | 6 => 2 | 7 => 2 | 8 => 4

private def pinXCoeff : Fin 3 → ℤ
  | 0 => 2 | 1 => -1 | 2 => -1

private def pinYCoeff : Fin 3 → ℤ
  | 0 => 0 | 1 => 1 | 2 => -1

private lemma cherryStepLen_pos (i : Fin 9) : 0 < cherryStepLen i := by
  revert i; decide

private lemma cherryStepLen_sq (i : Fin 9) :
    cherryDA i ^ 2 + 3 * cherryDB i ^ 2 = cherryStepLen i ^ 2 := by
  revert i; decide

private lemma cherryDA_eq_class (i : Fin 9) :
    2 * cherryDA i = cherryStepLen i * pinXCoeff (cherryPinClass i) := by
  revert i; decide

private lemma cherryDB_eq_class (i : Fin 9) :
    2 * cherryDB i = cherryStepLen i * pinYCoeff (cherryPinClass i) := by
  revert i; decide

private lemma cherry_unitDir_eq (i : Fin 9) :
    unitDir (cherryPinwheelPts (cherryEdges i).1.1) (cherryPinwheelPts (cherryEdges i).1.2) =
      pinDir (cherryPinClass i) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hL_pos : (0 : ℝ) < (cherryStepLen i : ℝ) := Int.cast_pos.mpr (cherryStepLen_pos i)
  have hL_ne : (cherryStepLen i : ℝ) ≠ 0 := hL_pos.ne'
  have hd0 : cherryPinwheelPts (cherryEdges i).1.2 0 - cherryPinwheelPts (cherryEdges i).1.1 0 =
      (cherryDA i : ℝ) := by
    simp only [cherryPinwheelPts, cherryDA, Int.cast_sub]
  have hd1 : cherryPinwheelPts (cherryEdges i).1.2 1 - cherryPinwheelPts (cherryEdges i).1.1 1 =
      (cherryDB i : ℝ) * Real.sqrt 3 := by
    simp only [cherryPinwheelPts, cherryDB, Int.cast_sub]; ring
  have hd2 : cherryPinwheelPts (cherryEdges i).1.2 2 - cherryPinwheelPts (cherryEdges i).1.1 2 = 0 := by
    simp only [cherryPinwheelPts, sub_self]
  have hnorm_sq : (cherryDA i : ℝ) ^ 2 + ((cherryDB i : ℝ) * Real.sqrt 3) ^ 2 + 0 ^ 2 =
      (cherryStepLen i : ℝ) ^ 2 := by
    have hZ : (cherryDA i : ℝ) ^ 2 + 3 * (cherryDB i : ℝ) ^ 2 = (cherryStepLen i : ℝ) ^ 2 := by
      exact_mod_cast cherryStepLen_sq i
    calc (cherryDA i : ℝ) ^ 2 + ((cherryDB i : ℝ) * Real.sqrt 3) ^ 2 + 0 ^ 2
        = (cherryDA i : ℝ) ^ 2 + Real.sqrt 3 ^ 2 * (cherryDB i : ℝ) ^ 2 := by ring
      _ = (cherryDA i : ℝ) ^ 2 + 3 * (cherryDB i : ℝ) ^ 2 := by rw [hs3]
      _ = (cherryStepLen i : ℝ) ^ 2 := hZ
  have heuclid : euclidNorm (fun k =>
      cherryPinwheelPts (cherryEdges i).1.2 k - cherryPinwheelPts (cherryEdges i).1.1 k) =
      (cherryStepLen i : ℝ) := by
    rw [euclidNorm, hd0, hd1, hd2, hnorm_sq, Real.sqrt_sq hL_pos.le]
  funext j
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [unitDir, heuclid, hd0]
    have h0R : 2 * (cherryDA i : ℝ) = (cherryStepLen i : ℝ) * (pinXCoeff (cherryPinClass i) : ℝ) := by
      exact_mod_cast cherryDA_eq_class i
    rcases fin3_cases (cherryPinClass i) with h | h | h <;> rw [h] at h0R ⊢ <;>
      simp only [pinDir, pinXCoeff, Int.cast_ofNat, Int.cast_neg, Int.cast_one] at h0R ⊢ <;>
      (field_simp [hL_ne]; linarith)
  · rw [unitDir, heuclid, hd1]
    have h1R : 2 * (cherryDB i : ℝ) = (cherryStepLen i : ℝ) * (pinYCoeff (cherryPinClass i) : ℝ) := by
      exact_mod_cast cherryDB_eq_class i
    rcases fin3_cases (cherryPinClass i) with h | h | h <;> rw [h] at h1R ⊢ <;>
      simp only [pinDir, pinYCoeff, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero,
        mul_one] at h1R ⊢
    · have hdb : (cherryDB i : ℝ) = 0 := by linarith
      rw [hdb, zero_mul, zero_div]
    · field_simp [hL_ne]; linarith [h1R]
    · field_simp [hL_ne]; linarith [h1R]
  · rw [unitDir, heuclid, hd2, zero_div]
    rcases fin3_cases (cherryPinClass i) with h | h | h <;> rw [h] <;> rfl

private def chNext : Fin 3 → Fin 3
  | 0 => 1 | 1 => 2 | 2 => 0

private def chRowCls (a c : Fin 3) : Fin 3 → Fin 3
  | 0 => a | 1 => chNext c | 2 => chNext c

private def chColCls (c : Fin 3) : Fin 3 → Fin 3
  | 0 => c | 1 => chNext c | 2 => chNext c

private lemma cherryPinClass_hub (a : Fin 3) :
    cherryPinClass (![0, 3, 6] a) = a := by
  fin_cases a <;> decide

private lemma cherryPinClass_block (c a : Fin 3) :
    cherryPinClass ⟨3 * c.val + a.val, by omega⟩ = chColCls c a := by
  revert c a; decide

private lemma cherry_prod_val (c j : Fin 3) :
    ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (c, j)).val = 3 * c.val + j.val := by
  revert c j; decide

private lemma cherryBlockPermFun_pair (τ : Fin 3 → Equiv.Perm (Fin 3)) (c j : Fin 3) :
    cherryBlockPermFun τ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (c, j)) =
      ⟨3 * c.val + (τ c j).val, by omega⟩ := by
  dsimp only [cherryBlockPermFun, Equiv.coe_fn_mk]
  rcases fin3_cases c with rfl | rfl | rfl
  · have hk := cherry_prod_val 0 j
    have hc0 : (0 : Fin 3).val = 0 := rfl
    rw [hc0] at hk
    have hlt : ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (0, j)).val < 3 := by omega
    simp only [hlt, ↓reduceDIte]
    apply Fin.ext; dsimp only
    have harg : (⟨((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (0, j)).val, hlt⟩ : Fin 3) = j :=
      Fin.ext (by dsimp only; omega)
    rw [harg]; simp only [Fin.val_zero, mul_zero, zero_add]
  · have hk := cherry_prod_val 1 j
    have hc1 : (1 : Fin 3).val = 1 := rfl
    rw [hc1] at hk
    have hn3 : ¬ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (1, j)).val < 3 := by omega
    have hlt : ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (1, j)).val < 6 := by omega
    simp only [hn3, ↓reduceDIte, hlt]
    apply Fin.ext; dsimp only
    have harg : (⟨((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (1, j)).val - 3, by omega⟩ : Fin 3) = j :=
      Fin.ext (by dsimp only; omega)
    rw [harg]; simp only [Fin.val_one, mul_one]
  · have hk := cherry_prod_val 2 j
    have hc2 : (2 : Fin 3).val = 2 := rfl
    rw [hc2] at hk
    have hn3 : ¬ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (2, j)).val < 3 := by omega
    have hn6 : ¬ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (2, j)).val < 6 := by omega
    simp only [hn3, ↓reduceDIte, hn6]
    apply Fin.ext; dsimp only
    have harg : (⟨((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (2, j)).val - 6, by omega⟩ : Fin 3) = j :=
      Fin.ext (by dsimp only; omega)
    rw [harg]
    have h2 : 3 * (2 : Fin 3).val = 6 := rfl
    rw [h2]

private lemma cherryHub_pinClass (π : Equiv.Perm (Fin 3)) (c j : Fin 3) :
    cherryPinClass (cherryHubPermFun π ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (c, j))) =
      chRowCls (π c) c j := by
  rcases fin3_cases c with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl
  · exact cherryPinClass_hub (π 0)
  · rfl
  · rfl
  · exact cherryPinClass_hub (π 1)
  · rfl
  · rfl
  · exact cherryPinClass_hub (π 2)
  · rfl
  · rfl

private noncomputable def pinGram (a b : Fin 3) : ℂ :=
  starRingEnd ℂ (pinSpinor a 0) * pinSpinor b 0 + starRingEnd ℂ (pinSpinor a 1) * pinSpinor b 1

private noncomputable def chVal (a c : Fin 3) : ℂ :=
  ∑ τ : Equiv.Perm (Fin 3), ∏ j : Fin 3, pinGram (chRowCls a c j) (chColCls c (τ j))

private lemma chVal_eval_all :
    omega3 ^ 3 = 1 ∧
    chVal 0 0 = 24 ∧ chVal 1 0 = -24 * omega3 ∧ chVal 2 0 = 0 ∧
    chVal 0 1 = 0 ∧ chVal 1 1 = 24 ∧ chVal 2 1 = -24 * omega3 ∧
    chVal 0 2 = -24 * omega3 ∧ chVal 1 2 = 0 ∧ chVal 2 2 = 24 := by
  have ho_conj : starRingEnd ℂ omega3 = -1 - omega3 := by
    apply Complex.ext <;>
      simp only [omega3, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
        Complex.neg_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im] <;>
      ring
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ho_sq : omega3 ^ 2 = -1 - omega3 := by
    apply Complex.ext
    · simp only [sq, Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.one_re,
        omega3, Complex.add_re, Complex.div_ofNat_re, Complex.add_im, Complex.div_ofNat_im,
        Complex.neg_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith [hs3]
    · simp only [sq, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.one_im,
        omega3, Complex.add_re, Complex.div_ofNat_re, Complex.add_im, Complex.div_ofNat_im,
        Complex.neg_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
  have ho_cube : omega3 ^ 3 = 1 := by linear_combination (omega3 - 1) * ho_sq
  have hG00 : pinGram 0 0 = 2 := by simp [pinGram, pinSpinor]; norm_num
  have hG11 : pinGram 1 1 = 2 := by simp [pinGram, pinSpinor, ho_conj]; linear_combination -ho_sq
  have hG22 : pinGram 2 2 = 2 := by simp [pinGram, pinSpinor, ho_conj]; linear_combination -ho_sq
  have hG01 : pinGram 0 1 = 1 + omega3 := by simp [pinGram, pinSpinor]
  have hG02 : pinGram 0 2 = -omega3 := by simp [pinGram, pinSpinor, ho_conj]; ring
  have hG10 : pinGram 1 0 = -omega3 := by simp [pinGram, pinSpinor, ho_conj]; ring
  have hG12 : pinGram 1 2 = 1 + omega3 := by simp [pinGram, pinSpinor, ho_conj]; linear_combination ho_sq
  have hG20 : pinGram 2 0 = 1 + omega3 := by simp [pinGram, pinSpinor, ho_conj]
  have hG21 : pinGram 2 1 = -omega3 := by simp [pinGram, pinSpinor, ho_conj]; linear_combination ho_sq
  have chVal_expand : ∀ a c : Fin 3, chVal a c =
      (pinGram (chRowCls a c 0) (chColCls c 0) * pinGram (chRowCls a c 1) (chColCls c 1) * pinGram (chRowCls a c 2) (chColCls c 2) +
       pinGram (chRowCls a c 0) (chColCls c 1) * pinGram (chRowCls a c 1) (chColCls c 0) * pinGram (chRowCls a c 2) (chColCls c 2) +
       pinGram (chRowCls a c 0) (chColCls c 0) * pinGram (chRowCls a c 1) (chColCls c 2) * pinGram (chRowCls a c 2) (chColCls c 1)) +
      (pinGram (chRowCls a c 0) (chColCls c 2) * pinGram (chRowCls a c 1) (chColCls c 1) * pinGram (chRowCls a c 2) (chColCls c 0) +
       pinGram (chRowCls a c 0) (chColCls c 1) * pinGram (chRowCls a c 1) (chColCls c 2) * pinGram (chRowCls a c 2) (chColCls c 0) +
       pinGram (chRowCls a c 0) (chColCls c 2) * pinGram (chRowCls a c 1) (chColCls c 0) * pinGram (chRowCls a c 2) (chColCls c 1)) := by
    intro a c
    dsimp only [chVal]
    rw [← Fintype.sum_equiv fin3PermCycEquiv _ _ (fun _ => rfl), Fin.sum_univ_six]
    simp only [fin3PermCycEquiv, Equiv.coe_fn_mk, fin3PermCycFun, Fin.prod_univ_three,
      Equiv.Perm.one_apply, Equiv.Perm.mul_apply]
    have hs01_0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
    have hs01_1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide
    have hs01_2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    have hs12_0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
    have hs12_1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
    have hs12_2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
    have hs02_0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
    have hs02_1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
    have hs02_2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide
    simp only [hs01_0, hs01_1, hs01_2, hs12_0, hs12_1, hs12_2, hs02_0, hs02_1, hs02_2]
    ring
  have hc00 : chVal 0 0 = 24 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG00, hG11, hG01, hG10]; linear_combination -8 * ho_sq
  have hc10 : chVal 1 0 = -24 * omega3 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG10, hG11]; ring
  have hc20 : chVal 2 0 = 0 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG20, hG11, hG21, hG10]; linear_combination 8 * ho_sq
  have hc01 : chVal 0 1 = 0 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG01, hG22, hG02, hG21]; linear_combination 8 * ho_sq
  have hc11 : chVal 1 1 = 24 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG11, hG22, hG12, hG21]; linear_combination -8 * ho_sq
  have hc21 : chVal 2 1 = -24 * omega3 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG21, hG22]; ring
  have hc02 : chVal 0 2 = -24 * omega3 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG02, hG00]; ring
  have hc12 : chVal 1 2 = 0 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG12, hG00, hG10, hG02]; linear_combination 8 * ho_sq
  have hc22 : chVal 2 2 = 24 := by
    rw [chVal_expand]; dsimp only [chRowCls, chColCls, chNext]
    rw [hG22, hG00, hG20, hG02]; linear_combination -8 * ho_sq
  exact ⟨ho_cube, hc00, hc10, hc20, hc01, hc11, hc21, hc02, hc12, hc22⟩

/-- **Exact Planar Zero on the Minimal 10-Vertex Cubic Cherry Tree `cherryTree10`:**
$\mathcal{A}_{T_{10}}(\mathbf{x}) = 0$ at `cherryPinwheelConfig` in $C_{T_{10}}(\mathbb{R}^3)$. -/
theorem malkounAmplitude_cherryPinwheel_eq_zero :
    malkounAmplitude cherryTree10 cherryPinwheelConfig = 0 := by
  let Φ : BipEdge cherryTree10 cherryPart → Fin 2 → ℂ :=
    fun e => pinSpinor (cherryPinClass (cherryEdgeEquiv.symm e))
  have hnorm : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = 2 := fun e => pinSpinor_norm_sq _
  have hmul : ∀ e, (pauliDot (unitDir (cherryPinwheelConfig.1 e.1.1) (cherryPinwheelConfig.1 e.1.2))).mulVec (Φ e) = Φ e := by
    intro e
    obtain ⟨i, rfl⟩ := cherryEdgeEquiv.surjective e
    have hΦ : Φ (cherryEdgeEquiv i) = pinSpinor (cherryPinClass i) := by
      simp only [Φ, Equiv.symm_apply_apply]
    have hdir : unitDir (cherryPinwheelConfig.1 (cherryEdgeEquiv i).1.1)
        (cherryPinwheelConfig.1 (cherryEdgeEquiv i).1.2) = pinDir (cherryPinClass i) :=
      cherry_unitDir_eq i
    rw [hΦ, hdir]
    exact pinSpinor_pauli (cherryPinClass i)
  rw [malkounAmplitude_bipartite_unnorm cherryTree10 cherryPart cherryTree10_isBipartite
      cherryPinwheelConfig Φ (fun _ => 2) (fun _ => by norm_num) hnorm hmul]
  obtain ⟨ho_cube, hc00, hc10, hc20, hc01, hc11, hc21, hc02, hc12, hc22⟩ := chVal_eval_all
  have hsum : (∑ σ₁ : bipP1 cherryTree10 cherryPart, ∑ σ₂ : bipP2 cherryTree10 cherryPart,
      ∏ e : BipEdge cherryTree10 cherryPart,
        (starRingEnd ℂ (Φ (σ₁.1 e) 0) * Φ (σ₂.1 e) 0 +
         starRingEnd ℂ (Φ (σ₁.1 e) 1) * Φ (σ₂.1 e) 1)) = 0 := by
    rw [← Fintype.sum_equiv cherryP1Equiv _ _ (fun _ => rfl)]
    simp_rw [← Fintype.sum_equiv cherryP2Equiv _ _ (fun _ => rfl)]
    have hprod_split : ∀ (π : Equiv.Perm (Fin 3)) (τ : Fin 3 → Equiv.Perm (Fin 3)),
        (∏ e : BipEdge cherryTree10 cherryPart,
          (starRingEnd ℂ (Φ ((cherryP1Equiv π).1 e) 0) * Φ ((cherryP2Equiv τ).1 e) 0 +
           starRingEnd ℂ (Φ ((cherryP1Equiv π).1 e) 1) * Φ ((cherryP2Equiv τ).1 e) 1)) =
        ∏ c : Fin 3, ∏ j : Fin 3, pinGram (chRowCls (π c) c j) (chColCls c (τ c j)) := by
      intro π τ
      rw [← Fintype.prod_equiv cherryEdgeEquiv _ _ (fun _ => rfl)]
      rw [← Fintype.prod_equiv (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) _ _ (fun _ => rfl)]
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun j _ => ?_
      have hr_eq : cherryPinClass (cherryHubPermFun π ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (c, j))) =
          chRowCls (π c) c j :=
        cherryHub_pinClass π c j
      have hc_eq : cherryPinClass (cherryBlockPermFun τ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (c, j))) =
          chColCls c (τ c j) := by
        rw [cherryBlockPermFun_pair, cherryPinClass_block]
      simp only [Φ, cherryP1Equiv, cherryP2Equiv, Equiv.coe_fn_mk,
        Equiv.permCongr_apply, Equiv.symm_apply_apply]
      change pinGram (cherryPinClass (cherryHubPermFun π ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (c, j))))
          (cherryPinClass (cherryBlockPermFun τ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) (c, j)))) =
        pinGram (chRowCls (π c) c j) (chColCls c (τ c j))
      rw [hr_eq, hc_eq]
    simp_rw [hprod_split]
    have hfac : ∀ π : Equiv.Perm (Fin 3),
        (∑ τ : Fin 3 → Equiv.Perm (Fin 3), ∏ c : Fin 3, ∏ j : Fin 3,
          pinGram (chRowCls (π c) c j) (chColCls c (τ c j))) =
        ∏ c : Fin 3, chVal (π c) c := fun π =>
      (Fintype.prod_sum fun c (τ_c : Equiv.Perm (Fin 3)) =>
        ∏ j : Fin 3, pinGram (chRowCls (π c) c j) (chColCls c (τ_c j))).symm
    simp_rw [hfac]
    rw [← Fintype.sum_equiv fin3PermCycEquiv _ _ (fun _ => rfl), Fin.sum_univ_six]
    simp only [fin3PermCycEquiv, Equiv.coe_fn_mk, fin3PermCycFun, Fin.prod_univ_three,
      Equiv.Perm.one_apply, Equiv.Perm.mul_apply]
    have hs01_0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
    have hs01_1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide
    have hs01_2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    have hs12_0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
    have hs12_1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
    have hs12_2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
    have hs02_0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
    have hs02_1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
    have hs02_2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide
    simp only [hs01_0, hs01_1, hs01_2, hs12_0, hs12_1, hs12_2, hs02_0, hs02_1, hs02_2]
    rw [hc00, hc11, hc22, hc10, hc01, hc20, hc12, hc02, hc21]
    linear_combination -13824 * ho_cube
  rw [hsum, map_zero, zero_div]

/-- **Formal Disproof of Malkoun's Conjecture C (Trees, `arXiv:2508.13472v3`, Section 4):**
`cherryTree10` is a 10-vertex connected tree with an explicit planar non-collision configuration
having zero amplitude $\mathcal{A}_{T_{10}}(\mathbf{x}) = 0$, violating $\operatorname{Re}(\mathcal{A}_T) \ge 1$. -/
theorem disproof_malkoun_conjecture_C : ¬ MalkounConjectureCProp := by
  intro hC
  have h := hC 10 cherryTree10 inferInstance cherryTree10_isTree cherryPinwheelConfig
  rw [malkounAmplitude_cherryPinwheel_eq_zero, Complex.zero_re] at h
  norm_num at h

/-- **Formal Disproof of Conjecture A Even Restricted to Finite Trees.** -/
theorem disproof_malkoun_tree_conjecture_A :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (_ : DecidableRel T.Adj) (x : ConfigSpace T),
      T.IsTree ∧ Function.Injective x.1 ∧ (∀ u, x.1 u 2 = 0) ∧ malkounAmplitude T x = 0 :=
  ⟨10, cherryTree10, inferInstance, cherryPinwheelConfig,
    cherryTree10_isTree, cherryPinwheelPts_injective, cherryPinwheel_planar,
    malkounAmplitude_cherryPinwheel_eq_zero⟩

/-- **Formal Disproof of Conjecture B Even Restricted to Finite Trees.** -/
theorem disproof_malkoun_tree_conjecture_B :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (_ : DecidableRel T.Adj) (x : ConfigSpace T),
      T.IsTree ∧ ‖malkounAmplitude T x‖ < 1 := by
  refine ⟨10, cherryTree10, inferInstance, cherryPinwheelConfig, cherryTree10_isTree, ?_⟩
  rw [malkounAmplitude_cherryPinwheel_eq_zero, norm_zero]
  norm_num

/-- **Formal Disproof of Tree-Restricted Conjecture D (`MalkounTreeConjectureDProp`):**
by `treeConjectureD_implies_conjecture_C`, the planar zero on `cherryTree10` refutes Conjecture D
even when restricted to tree bipartitions and rank-2 complex matrices. -/
theorem disproof_malkoun_tree_conjecture_D : ¬ MalkounTreeConjectureDProp := by
  intro hTD
  have h := (treeConjectureD_implies_conjecture_C hTD cherryTree10 cherryTree10_isTree cherryPinwheelConfig).1
  rw [malkounAmplitude_cherryPinwheel_eq_zero, Complex.zero_re] at h
  norm_num at h

end CherryTree10

/-! ## Part 3: Strictly Negative Real Part on Malkoun's Path Family $LG_{15}$ (`pathGraph15`) -/

section PathGraph15NegRe

/-- Linear path graph $LG_{15}$ on `Fin 15` ($m = 14$ edges). -/
def pathGraph15 : SimpleGraph (Fin 15) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance instDecidableRelPath15 : DecidableRel pathGraph15.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)))

theorem pathGraph15_connected : pathGraph15.Connected := by
  have hr : ∀ (k : ℕ) (hk : k < 15), pathGraph15.Reachable 0 ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl 0
    | succ k ih =>
        intro hk
        have hadj : pathGraph15.Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ := Or.inl rfl
        exact (ih (by omega)).trans hadj.reachable
  exact ⟨fun u v => (hr u.val u.isLt).symm.trans (hr v.val v.isLt)⟩

theorem pathGraph15_isTree : pathGraph15.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨pathGraph15_connected, ?_⟩
  rw [Nat.card_coe_set_eq, ← SimpleGraph.coe_edgeFinset pathGraph15, Set.ncard_coe_finset,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

/-- Alternating vertex bipartition on `Fin 15`: odd vertices `false`, even vertices `true`. -/
def partEvenTrue (u : Fin 15) : Bool := decide (u.val % 2 = 0)

lemma path15_isBipartite : IsBipartite pathGraph15 partEvenTrue := by
  intro u v huv
  rcases huv with h | h <;> simp [partEvenTrue] <;> omega

private def path15EdgeEnd (e : Fin 14) : Fin 15 × Fin 15 :=
  if e.val % 2 = 0 then (⟨e.val + 1, by omega⟩, ⟨e.val, by omega⟩)
  else (⟨e.val, by omega⟩, ⟨e.val + 1, by omega⟩)

private def path15Edges (e : Fin 14) : BipEdge pathGraph15 partEvenTrue :=
  ⟨path15EdgeEnd e, by
    unfold path15EdgeEnd
    split_ifs with h
    · refine ⟨Or.inr rfl, ?_, ?_⟩ <;> simp [partEvenTrue] <;> omega
    · refine ⟨Or.inl rfl, ?_, ?_⟩ <;> simp [partEvenTrue] <;> omega⟩

private def path15EdgeEquiv : Fin 14 ≃ BipEdge pathGraph15 partEvenTrue where
  toFun := path15Edges
  invFun e := ⟨min e.1.1.val e.1.2.val, by
    rcases e with ⟨⟨⟨uv, huv⟩, ⟨vv, hvv⟩⟩, hadj, _⟩
    dsimp only at hadj ⊢
    rcases hadj with h | h <;> simp only at h ⊢ <;> omega⟩
  left_inv e := by
    apply Fin.ext
    dsimp only [path15Edges, path15EdgeEnd]
    split_ifs <;> simp
  right_inv e := by
    apply Subtype.ext
    rcases e with ⟨⟨⟨uv, huv⟩, ⟨vv, hvv⟩⟩, hadj, hu, hv⟩
    dsimp only [path15Edges, path15EdgeEnd]
    simp only [partEvenTrue, decide_eq_false_iff_not, decide_eq_true_eq] at hu hv
    rcases hadj with h | h <;>
      simp only at h <;>
      split_ifs <;>
      exact Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega))

private lemma path15P1Perm_invol (b : Fin 7 → Bool) (e : Fin 14) :
    (fun x : Fin 14 => if b ⟨x.val / 2, by omega⟩ then ⟨2 * (x.val / 2) + (1 - x.val % 2), by omega⟩ else x)
      ((fun x : Fin 14 => if b ⟨x.val / 2, by omega⟩ then ⟨2 * (x.val / 2) + (1 - x.val % 2), by omega⟩ else x) e) = e := by
  dsimp only
  by_cases h : b ⟨e.val / 2, by omega⟩ = true
  · simp only [h, ↓reduceIte]
    have hdiv : (2 * (e.val / 2) + (1 - e.val % 2)) / 2 = e.val / 2 := by omega
    have hidx : (⟨(2 * (e.val / 2) + (1 - e.val % 2)) / 2, by omega⟩ : Fin 7) =
        ⟨e.val / 2, by omega⟩ := Fin.ext hdiv
    rw [hidx]
    simp only [h, ↓reduceIte]
    apply Fin.ext; dsimp only; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

private def path15P1Perm (b : Fin 7 → Bool) : Equiv.Perm (Fin 14) where
  toFun e := if b ⟨e.val / 2, by omega⟩ then ⟨2 * (e.val / 2) + (1 - e.val % 2), by omega⟩ else e
  invFun e := if b ⟨e.val / 2, by omega⟩ then ⟨2 * (e.val / 2) + (1 - e.val % 2), by omega⟩ else e
  left_inv e := path15P1Perm_invol b e
  right_inv e := path15P1Perm_invol b e

private lemma path15Edges_fst_val (i : Fin 14) :
    (path15Edges i).1.1.val = 2 * (i.val / 2) + 1 := by
  revert i; decide

private lemma path15Edges_snd_val (i : Fin 14) :
    (path15Edges i).1.2.val = if i.val = 0 then 0 else if i.val = 13 then 14 else 2 * ((i.val - 1) / 2) + 2 := by
  revert i; decide

private def path15P1Equiv : (Fin 7 → Bool) ≃ bipP1 pathGraph15 partEvenTrue where
  toFun b := ⟨Equiv.permCongr path15EdgeEquiv (path15P1Perm b), fun e => by
    obtain ⟨i, rfl⟩ := path15EdgeEquiv.surjective e
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply Fin.ext
    change (path15Edges (path15P1Perm b i)).1.1.val = (path15Edges i).1.1.val
    rw [path15Edges_fst_val, path15Edges_fst_val]
    dsimp only [path15P1Perm, Equiv.coe_fn_mk]
    by_cases hb : b ⟨i.val / 2, by omega⟩ = true
    · simp only [hb, ↓reduceIte]; omega
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]⟩
  invFun σ := fun j =>
    decide ((Equiv.permCongr path15EdgeEquiv.symm σ.1) ⟨2 * j.val, by omega⟩ ≠ ⟨2 * j.val, by omega⟩)
  left_inv b := by
    funext j
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      path15P1Perm, Equiv.coe_fn_mk]
    have hdiv : (2 * j.val) / 2 = j.val := by omega
    have hidx : (⟨(2 * j.val) / 2, by omega⟩ : Fin 7) = j := Fin.ext hdiv
    rw [hidx]
    cases h : b j
    · simp
    · simp only [↓reduceIte, ne_eq, decide_eq_true_eq]
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    obtain ⟨i, rfl⟩ := path15EdgeEquiv.surjective e
    let σ' := Equiv.permCongr path15EdgeEquiv.symm σ.1
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change path15Edges (path15P1Perm _ i) = σ.1 (path15Edges i)
    have hdiv_all : ∀ k : Fin 14, (σ' k).val / 2 = k.val / 2 := by
      intro k
      have hfst : (σ.1 (path15Edges k)).1.1.val = (path15Edges k).1.1.val :=
        congrArg Fin.val (σ.2 (path15Edges k))
      have hc' : σ' k = path15EdgeEquiv.symm (σ.1 (path15Edges k)) := rfl
      have hback : path15Edges (σ' k) = σ.1 (path15Edges k) := by
        rw [hc']; exact path15EdgeEquiv.apply_symm_apply _
      rw [← hback, path15Edges_fst_val, path15Edges_fst_val] at hfst
      omega
    let j : Fin 7 := ⟨i.val / 2, by omega⟩
    let i0 : Fin 14 := ⟨2 * j.val, by omega⟩
    let i1 : Fin 14 := ⟨2 * j.val + 1, by omega⟩
    have hj0 := hdiv_all i0
    have hj1 := hdiv_all i1
    have hmod0 : i0.val / 2 = j.val := by dsimp only [i0]; omega
    have hmod1 : i1.val / 2 = j.val := by dsimp only [i1]; omega
    have hcases0 : σ' i0 = i0 ∨ σ' i0 = i1 := by
      rcases (by omega : (σ' i0).val = 2 * j.val ∨ (σ' i0).val = 2 * j.val + 1) with h | h
      · left; exact Fin.ext (by simp [i0]; exact h)
      · right; exact Fin.ext (by simp [i1]; exact h)
    have hcases1 : σ' i1 = i0 ∨ σ' i1 = i1 := by
      rcases (by omega : (σ' i1).val = 2 * j.val ∨ (σ' i1).val = 2 * j.val + 1) with h | h
      · left; exact Fin.ext (by simp [i0]; exact h)
      · right; exact Fin.ext (by simp [i1]; exact h)
    have hne : σ' i0 ≠ σ' i1 := fun h => by
      have hinj := σ'.injective h
      have hv := congrArg Fin.val hinj
      simp [i0, i1] at hv
    have hj_v : j.val = i.val / 2 := rfl
    have hi_cases : i = i0 ∨ i = i1 := by
      rcases (by omega : i.val = 2 * j.val ∨ i.val = 2 * j.val + 1) with h | h
      · left; exact Fin.ext (by simp [i0]; exact h)
      · right; exact Fin.ext (by simp [i1]; exact h)
    dsimp only [path15P1Perm, Equiv.coe_fn_mk]
    rcases hcases0 with h00 | h01 <;> rcases hcases1 with h10 | h11
    · exact absurd (h00.trans h10.symm) hne
    · have hc : decide (σ' i0 ≠ i0) = false := decide_eq_false (not_not.mpr h00)
      have heq_main : (if decide (σ' i0 ≠ i0) then (⟨2 * j.val + (1 - i.val % 2), by omega⟩ : Fin 14) else i) = σ' i := by
        rw [hc]
        rcases hi_cases with hi0 | hi1
        · exact (hi0.trans h00.symm).trans (congrArg σ' hi0.symm)
        · exact (hi1.trans h11.symm).trans (congrArg σ' hi1.symm)
      change path15Edges (if decide (σ' i0 ≠ i0) then _ else i) = _
      rw [heq_main]
      exact path15EdgeEquiv.apply_symm_apply _
    · have h01ne : σ' i0 ≠ i0 := fun h => by
        have hv := congrArg Fin.val (h01.symm.trans h)
        simp [i0, i1] at hv
      have hc : decide (σ' i0 ≠ i0) = true := decide_eq_true h01ne
      have heq_main : (if decide (σ' i0 ≠ i0) then (⟨2 * j.val + (1 - i.val % 2), by omega⟩ : Fin 14) else i) = σ' i := by
        rw [hc]
        simp only [↓reduceIte]
        apply Fin.ext; dsimp only
        rcases hi_cases with hi0 | hi1
        · have hiv := congrArg Fin.val hi0
          have hσv := congrArg Fin.val (congrArg σ' hi0)
          rw [h01] at hσv
          dsimp only [i0, i1] at hiv hσv
          omega
        · have hiv := congrArg Fin.val hi1
          have hσv := congrArg Fin.val (congrArg σ' hi1)
          rw [h10] at hσv
          dsimp only [i0, i1] at hiv hσv
          omega
      change path15Edges (if decide (σ' i0 ≠ i0) then _ else _) = _
      rw [heq_main]
      exact path15EdgeEquiv.apply_symm_apply _
    · exact absurd (h01.trans h11.symm) hne

private lemma path15P2Perm_invol (b : Fin 6 → Bool) (e : Fin 14) :
    (fun x : Fin 14 =>
      if h1 : 1 ≤ x.val ∧ x.val ≤ 12 then
        if b ⟨(x.val - 1) / 2, by omega⟩ then
          ⟨2 * ((x.val - 1) / 2) + 1 + (1 - (x.val - 1) % 2), by omega⟩
        else x
      else x)
    ((fun x : Fin 14 =>
      if h1 : 1 ≤ x.val ∧ x.val ≤ 12 then
        if b ⟨(x.val - 1) / 2, by omega⟩ then
          ⟨2 * ((x.val - 1) / 2) + 1 + (1 - (x.val - 1) % 2), by omega⟩
        else x
      else x) e) = e := by
  dsimp only
  by_cases h1 : 1 ≤ e.val ∧ e.val ≤ 12
  · simp only [h1.1, h1.2, and_self, ↓reduceDIte]
    by_cases hb : b ⟨(e.val - 1) / 2, by omega⟩ = true
    · simp only [hb, ↓reduceIte]
      have h1' : 1 ≤ (⟨2 * ((e.val - 1) / 2) + 1 + (1 - (e.val - 1) % 2), by omega⟩ : Fin 14).val ∧
          (⟨2 * ((e.val - 1) / 2) + 1 + (1 - (e.val - 1) % 2), by omega⟩ : Fin 14).val ≤ 12 :=
        ⟨by dsimp only; omega, by dsimp only; omega⟩
      simp only [h1'.1, h1'.2, and_self, ↓reduceDIte]
      have hidx : (⟨(2 * ((e.val - 1) / 2) + 1 + (1 - (e.val - 1) % 2) - 1) / 2, by omega⟩ : Fin 6) =
          ⟨(e.val - 1) / 2, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hidx]
      simp only [hb, ↓reduceIte]
      apply Fin.ext; dsimp only; omega
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, h1.1, h1.2, and_self, ↓reduceDIte]
  · simp only [h1, ↓reduceDIte]

private def path15P2Perm (b : Fin 6 → Bool) : Equiv.Perm (Fin 14) where
  toFun e :=
    if h1 : 1 ≤ e.val ∧ e.val ≤ 12 then
      if b ⟨(e.val - 1) / 2, by omega⟩ then ⟨2 * ((e.val - 1) / 2) + 1 + (1 - (e.val - 1) % 2), by omega⟩
      else e
    else e
  invFun e :=
    if h1 : 1 ≤ e.val ∧ e.val ≤ 12 then
      if b ⟨(e.val - 1) / 2, by omega⟩ then ⟨2 * ((e.val - 1) / 2) + 1 + (1 - (e.val - 1) % 2), by omega⟩
      else e
    else e
  left_inv e := path15P2Perm_invol b e
  right_inv e := path15P2Perm_invol b e

private def path15P2Equiv : (Fin 6 → Bool) ≃ bipP2 pathGraph15 partEvenTrue where
  toFun b := ⟨Equiv.permCongr path15EdgeEquiv (path15P2Perm b), fun e => by
    obtain ⟨i, rfl⟩ := path15EdgeEquiv.surjective e
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply Fin.ext
    change (path15Edges (path15P2Perm b i)).1.2.val = (path15Edges i).1.2.val
    rw [path15Edges_snd_val, path15Edges_snd_val]
    dsimp only [path15P2Perm, Equiv.coe_fn_mk]
    by_cases h1 : 1 ≤ i.val ∧ i.val ≤ 12
    · simp only [h1.1, h1.2, and_self, ↓reduceDIte]
      by_cases hb : b ⟨(i.val - 1) / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]
        have hk0 : ¬ (2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2) = 0) := by omega
        have hk13 : ¬ (2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2) = 13) := by omega
        have hi0 : i.val ≠ 0 := by omega
        have hi13 : i.val ≠ 13 := by omega
        simp only [hk0, hk13, hi0, hi13, ↓reduceIte]
        omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    · simp only [h1, ↓reduceDIte]⟩
  invFun σ := fun j =>
    decide ((Equiv.permCongr path15EdgeEquiv.symm σ.1) ⟨2 * j.val + 1, by omega⟩ ≠ ⟨2 * j.val + 1, by omega⟩)
  left_inv b := by
    funext j
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      path15P2Perm, Equiv.coe_fn_mk]
    have h1 : 1 ≤ (⟨2 * j.val + 1, by omega⟩ : Fin 14).val ∧
        (⟨2 * j.val + 1, by omega⟩ : Fin 14).val ≤ 12 := ⟨by dsimp only; omega, by dsimp only; omega⟩
    simp only [h1.1, h1.2, and_self, ↓reduceDIte]
    have hidx : (⟨((2 * j.val + 1) - 1) / 2, by omega⟩ : Fin 6) = j := Fin.ext (by dsimp only; omega)
    rw [hidx]
    cases h : b j
    · simp
    · simp only [↓reduceIte, ne_eq, decide_eq_true_eq]
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    obtain ⟨i, rfl⟩ := path15EdgeEquiv.surjective e
    let σ' := Equiv.permCongr path15EdgeEquiv.symm σ.1
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change path15Edges (path15P2Perm _ i) = σ.1 (path15Edges i)
    have hsnd_val : ∀ k : Fin 14, (path15Edges (σ' k)).1.2.val = (path15Edges k).1.2.val := fun k => by
      have hc' : σ' k = path15EdgeEquiv.symm (σ.1 (path15Edges k)) := rfl
      have hback : path15Edges (σ' k) = σ.1 (path15Edges k) := by
        rw [hc']; exact path15EdgeEquiv.apply_symm_apply _
      rw [hback]
      exact congrArg Fin.val (σ.2 (path15Edges k))
    have hfix0 : σ' 0 = 0 := by
      have h := hsnd_val 0
      have hlt := (σ' 0).isLt
      rw [path15Edges_snd_val, path15Edges_snd_val] at h
      simp only [Fin.val_zero, ↓reduceIte] at h
      split_ifs at h with h0 h13
      exact Fin.ext h0
    have hfix13 : σ' 13 = 13 := by
      have h := hsnd_val 13
      have hlt := (σ' 13).isLt
      rw [path15Edges_snd_val, path15Edges_snd_val] at h
      have h13v : (13 : Fin 14).val = 13 := rfl
      simp only [h13v, show ¬ (13 : ℕ) = 0 by decide, ↓reduceIte] at h
      split_ifs at h with h0 h13 <;> first | exact Fin.ext h13 | omega
    have hpair : ∀ k : Fin 14, 1 ≤ k.val → k.val ≤ 12 →
        1 ≤ (σ' k).val ∧ (σ' k).val ≤ 12 ∧ ((σ' k).val - 1) / 2 = (k.val - 1) / 2 := by
      intro k hk1 hk12
      have h0ne : σ' k ≠ 0 := fun heq => by
        have hk0 := σ'.injective (heq.trans hfix0.symm)
        have hv := congrArg Fin.val hk0
        omega
      have h13ne : σ' k ≠ 13 := fun heq => by
        have hk13 := σ'.injective (heq.trans hfix13.symm)
        have hv := congrArg Fin.val hk13
        omega
      have hne0 : (σ' k).val ≠ 0 := fun hv => h0ne (Fin.ext hv)
      have hne13 : (σ' k).val ≠ 13 := fun hv => h13ne (Fin.ext hv)
      have hs := hsnd_val k
      rw [path15Edges_snd_val, path15Edges_snd_val] at hs
      have hkne0 : k.val ≠ 0 := by omega
      have hkne13 : k.val ≠ 13 := by omega
      simp only [hne0, hne13, hkne0, hkne13, ↓reduceIte] at hs
      refine ⟨by omega, by omega, by omega⟩
    dsimp only [path15P2Perm, Equiv.coe_fn_mk]
    by_cases h1 : 1 ≤ i.val ∧ i.val ≤ 12
    · simp only [h1.1, h1.2, and_self, ↓reduceDIte]
      let j : Fin 6 := ⟨(i.val - 1) / 2, by omega⟩
      let i0 : Fin 14 := ⟨2 * j.val + 1, by omega⟩
      let i1 : Fin 14 := ⟨2 * j.val + 2, by omega⟩
      have hj_v : j.val = (i.val - 1) / 2 := rfl
      have hi0_v : i0.val = 2 * j.val + 1 := rfl
      have hi1_v : i1.val = 2 * j.val + 2 := rfl
      have hp0 := hpair i0 (by omega) (by omega)
      have hp1 := hpair i1 (by omega) (by omega)
      have hcases0 : σ' i0 = i0 ∨ σ' i0 = i1 := by
        have hv0 : (σ' i0).val = 2 * j.val + 1 ∨ (σ' i0).val = 2 * j.val + 2 := by omega
        rcases hv0 with h | h
        · left; exact Fin.ext (by simp [i0]; exact h)
        · right; exact Fin.ext (by simp [i1]; exact h)
      have hcases1 : σ' i1 = i0 ∨ σ' i1 = i1 := by
        have hv1 : (σ' i1).val = 2 * j.val + 1 ∨ (σ' i1).val = 2 * j.val + 2 := by omega
        rcases hv1 with h | h
        · left; exact Fin.ext (by simp [i0]; exact h)
        · right; exact Fin.ext (by simp [i1]; exact h)
      have hne : σ' i0 ≠ σ' i1 := fun h => by
        have hv := congrArg Fin.val (σ'.injective h)
        simp [i0, i1] at hv
      have hi_cases : i = i0 ∨ i = i1 := by
        rcases (by omega : i.val = 2 * j.val + 1 ∨ i.val = 2 * j.val + 2) with h | h
        · left; exact Fin.ext (by simp [i0]; exact h)
        · right; exact Fin.ext (by simp [i1]; exact h)
      have hmid : (if decide (σ' i0 ≠ i0) then (⟨2 * j.val + 1 + (1 - (i.val - 1) % 2), by omega⟩ : Fin 14) else i) = σ' i := by
        rcases hcases0 with h00 | h01 <;> rcases hcases1 with h10 | h11
        · exact absurd (h00.trans h10.symm) hne
        · have hc : decide (σ' i0 ≠ i0) = false := decide_eq_false (not_not.mpr h00)
          rw [hc]
          rcases hi_cases with hi0 | hi1
          · exact (hi0.trans h00.symm).trans (congrArg σ' hi0.symm)
          · exact (hi1.trans h11.symm).trans (congrArg σ' hi1.symm)
        · have h01ne : σ' i0 ≠ i0 := fun h => by
            have hv := congrArg Fin.val (h01.symm.trans h)
            simp [i0, i1] at hv
          have hc : decide (σ' i0 ≠ i0) = true := decide_eq_true h01ne
          rw [hc]
          simp only [↓reduceIte]
          apply Fin.ext; dsimp only
          rcases hi_cases with hi0 | hi1
          · have hiv := congrArg Fin.val hi0
            have hσv := congrArg Fin.val (congrArg σ' hi0)
            rw [h01] at hσv
            dsimp only [i0, i1] at hiv hσv
            omega
          · have hiv := congrArg Fin.val hi1
            have hσv := congrArg Fin.val (congrArg σ' hi1)
            rw [h10] at hσv
            dsimp only [i0, i1] at hiv hσv
            omega
        · exact absurd (h01.trans h11.symm) hne
      change path15Edges (if decide (σ' i0 ≠ i0) then _ else i) = σ.1 (path15Edges i)
      rw [hmid]
      exact path15EdgeEquiv.apply_symm_apply _
    · simp only [h1, ↓reduceDIte]
      have hi013 : i = 0 ∨ i = 13 := by
        rcases (by omega : i.val = 0 ∨ i.val = 13) with h | h
        · left; exact Fin.ext h
        · right; exact Fin.ext h
      rcases hi013 with rfl | rfl
      · change path15Edges 0 = σ.1 (path15Edges 0)
        conv_lhs => rw [← hfix0]
        exact path15EdgeEquiv.apply_symm_apply _
      · change path15Edges 13 = σ.1 (path15Edges 13)
        conv_lhs => rw [← hfix13]
        exact path15EdgeEquiv.apply_symm_apply _

/-- Gram entry for `path15` spinor matrix `BGI : Fin 2 → Fin 14 → GI`. -/
def path15GramGI (BGI : Fin 2 → Fin 14 → GI) (a b : Fin 14) : GI :=
  sumFinGI 2 fun i => starGI (BGI i a) * BGI i b

/-- $2 \times 2$ transfer block at pair index `j : Fin 7` combining edges `2j` and `2j + 1`. -/
def path15BlockGI (BGI : Fin 2 → Fin 14 → GI) (j : Fin 7) (bL bR : Bool) : GI :=
  let e0 : Fin 14 := ⟨2 * j.val, by omega⟩
  let e1 : Fin 14 := ⟨2 * j.val + 1, by omega⟩
  let c0 : Fin 14 := if h : bL = true ∧ 0 < j.val then ⟨2 * j.val - 1, by omega⟩ else e0
  let c1 : Fin 14 := if h : bR = true ∧ j.val < 6 then ⟨2 * j.val + 2, by omega⟩ else e1
  path15GramGI BGI e0 c0 * path15GramGI BGI e1 c1 +
  path15GramGI BGI e1 c0 * path15GramGI BGI e0 c1

/-- Exact $2 \times 2$ transfer-matrix chain contraction in `GI`. -/
def matProdGI : ∀ k : ℕ, (Fin (k + 1) → Bool → Bool → GI) → Bool → Bool → GI
  | 0, F, a, c => F 0 a c
  | k + 1, F, a, c =>
      F 0 a false * matProdGI k (fun j => F j.succ) false c +
      F 0 a true * matProdGI k (fun j => F j.succ) true c

private def matChainC : ∀ k : ℕ, (Fin (k + 1) → Bool → Bool → ℂ) → (Fin k → Bool) → Bool → Bool → ℂ
  | 0, F, _, a, c => F 0 a c
  | k + 1, F, b, a, c =>
      F 0 a (b 0) * matChainC k (fun j => F j.succ) (fun j => b j.succ) (b 0) c

private lemma matProdC_eq_sum :
    ∀ (k : ℕ) (FGI : Fin (k + 1) → Bool → Bool → GI) (a c : Bool),
      GI.toC (matProdGI k FGI a c) =
        ∑ b : Fin k → Bool,
          matChainC k (fun j x y => GI.toC (FGI j x y)) b a c
  | 0, FGI, a, c => by
      simp [matProdGI, matChainC]
  | k + 1, FGI, a, c => by
      simp only [matProdGI, GI.toC_add, GI.toC_mul, matProdC_eq_sum k]
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Bool))
        (fun p => GI.toC (FGI 0 a p.1) *
          matChainC k (fun j x y => GI.toC (FGI j.succ x y)) p.2 p.1 c)
        (fun b => matChainC (k + 1) (fun j x y => GI.toC (FGI j x y)) b a c)
        (fun _ => rfl)]
      rw [Fintype.sum_prod_type, sum_bool_ft, Finset.mul_sum, Finset.mul_sum]

private def bitLeft (b₂ : Fin 6 → Bool) (j : Fin 7) : Bool :=
  if h : 0 < j.val then b₂ ⟨j.val - 1, by omega⟩ else false

private def bitRight (b₂ : Fin 6 → Bool) (j : Fin 7) : Bool :=
  if h : j.val < 6 then b₂ ⟨j.val, h⟩ else false

private lemma matChain6_eq_prod (F : Fin 7 → Bool → Bool → ℂ) (b₂ : Fin 6 → Bool) :
    matChainC 6 F b₂ false false = ∏ j : Fin 7, F j (bitLeft b₂ j) (bitRight b₂ j) := by
  have hL0 : bitLeft b₂ 0 = false := rfl
  have hL1 : bitLeft b₂ 1 = b₂ 0 := rfl
  have hL2 : bitLeft b₂ 2 = b₂ 1 := rfl
  have hL3 : bitLeft b₂ 3 = b₂ 2 := rfl
  have hL4 : bitLeft b₂ 4 = b₂ 3 := rfl
  have hL5 : bitLeft b₂ 5 = b₂ 4 := rfl
  have hL6 : bitLeft b₂ 6 = b₂ 5 := rfl
  have hR0 : bitRight b₂ 0 = b₂ 0 := rfl
  have hR1 : bitRight b₂ 1 = b₂ 1 := rfl
  have hR2 : bitRight b₂ 2 = b₂ 2 := rfl
  have hR3 : bitRight b₂ 3 = b₂ 3 := rfl
  have hR4 : bitRight b₂ 4 = b₂ 4 := rfl
  have hR5 : bitRight b₂ 5 = b₂ 5 := rfl
  have hR6 : bitRight b₂ 6 = false := rfl
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change F 0 false (b₂ 0) * (F 1 (b₂ 0) (b₂ 1) * (F 2 (b₂ 1) (b₂ 2) *
      (F 3 (b₂ 2) (b₂ 3) * (F 4 (b₂ 3) (b₂ 4) * (F 5 (b₂ 4) (b₂ 5) * F 6 (b₂ 5) false))))) =
    F 0 (bitLeft b₂ 0) (bitRight b₂ 0) * (F 1 (bitLeft b₂ 1) (bitRight b₂ 1) *
      (F 2 (bitLeft b₂ 2) (bitRight b₂ 2) * (F 3 (bitLeft b₂ 3) (bitRight b₂ 3) *
        (F 4 (bitLeft b₂ 4) (bitRight b₂ 4) * (F 5 (bitLeft b₂ 5) (bitRight b₂ 5) *
          F 6 (bitLeft b₂ 6) (bitRight b₂ 6))))))
  rw [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hR0, hR1, hR2, hR3, hR4, hR5, hR6]

theorem path15_gram_sum_eq_toC (BGI : Fin 2 → Fin 14 → GI) :
    (∑ σ₁ : bipP1 pathGraph15 partEvenTrue, ∑ σ₂ : bipP2 pathGraph15 partEvenTrue,
      ∏ e : BipEdge pathGraph15 partEvenTrue,
        (starRingEnd ℂ (GI.toC (BGI 0 (path15EdgeEquiv.symm (σ₁.1 e)))) *
          GI.toC (BGI 0 (path15EdgeEquiv.symm (σ₂.1 e))) +
         starRingEnd ℂ (GI.toC (BGI 1 (path15EdgeEquiv.symm (σ₁.1 e)))) *
          GI.toC (BGI 1 (path15EdgeEquiv.symm (σ₂.1 e))))) =
    GI.toC (matProdGI 6 (path15BlockGI BGI) false false) := by
  let H : Fin 14 → Fin 14 → ℂ := fun a b => GI.toC (path15GramGI BGI a b)
  have hH : ∀ a b,
      starRingEnd ℂ (GI.toC (BGI 0 a)) * GI.toC (BGI 0 b) +
      starRingEnd ℂ (GI.toC (BGI 1 a)) * GI.toC (BGI 1 b) = H a b := by
    intro a b
    simp only [H, path15GramGI, toC_sumFinGI', Fin.sum_univ_two, GI.toC_mul, toC_starGI']
  rw [← Fintype.sum_equiv path15P1Equiv _ _ (fun _ => rfl)]
  rw [Finset.sum_comm]
  rw [← Fintype.sum_equiv path15P2Equiv _ _ (fun _ => rfl)]
  have hprod_b : ∀ (b₂ : Fin 6 → Bool) (b₁ : Fin 7 → Bool),
      (∏ e : BipEdge pathGraph15 partEvenTrue,
        (starRingEnd ℂ (GI.toC (BGI 0 (path15EdgeEquiv.symm ((path15P1Equiv b₁).1 e)))) *
          GI.toC (BGI 0 (path15EdgeEquiv.symm ((path15P2Equiv b₂).1 e))) +
         starRingEnd ℂ (GI.toC (BGI 1 (path15EdgeEquiv.symm ((path15P1Equiv b₁).1 e)))) *
          GI.toC (BGI 1 (path15EdgeEquiv.symm ((path15P2Equiv b₂).1 e))))) =
      ∏ j : Fin 7,
        (if b₁ j then
          H ⟨2 * j.val + 1, by omega⟩ (if h : bitLeft b₂ j = true ∧ 0 < j.val then ⟨2 * j.val - 1, by omega⟩ else ⟨2 * j.val, by omega⟩) *
          H ⟨2 * j.val, by omega⟩ (if h : bitRight b₂ j = true ∧ j.val < 6 then ⟨2 * j.val + 2, by omega⟩ else ⟨2 * j.val + 1, by omega⟩)
        else
          H ⟨2 * j.val, by omega⟩ (if h : bitLeft b₂ j = true ∧ 0 < j.val then ⟨2 * j.val - 1, by omega⟩ else ⟨2 * j.val, by omega⟩) *
          H ⟨2 * j.val + 1, by omega⟩ (if h : bitRight b₂ j = true ∧ j.val < 6 then ⟨2 * j.val + 2, by omega⟩ else ⟨2 * j.val + 1, by omega⟩)) := by
    intro b₂ b₁
    rw [← Fintype.prod_equiv path15EdgeEquiv _ _ (fun _ => rfl)]
    rw [← Fintype.prod_equiv (finProdFinEquiv : Fin 7 × Fin 2 ≃ Fin 14) _ _ (fun _ => rfl)]
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_two]
    let idx0 : Fin 14 := (finProdFinEquiv : Fin 7 × Fin 2 ≃ Fin 14) (j, 0)
    let idx1 : Fin 14 := (finProdFinEquiv : Fin 7 × Fin 2 ≃ Fin 14) (j, 1)
    have hidx0 : idx0.val = 2 * j.val := by dsimp [idx0, finProdFinEquiv]; omega
    have hidx1 : idx1.val = 2 * j.val + 1 := by dsimp [idx1, finProdFinEquiv]; omega
    have hl_simp : path15P1Perm b₁ idx0 =
        (if b₁ j then ⟨2 * j.val + 1, by omega⟩ else ⟨2 * j.val, by omega⟩) := by
      dsimp only [path15P1Perm, Equiv.coe_fn_mk]
      have harg : (⟨idx0.val / 2, by omega⟩ : Fin 7) = j := Fin.ext (by dsimp only; omega)
      rw [harg]
      cases b₁ j
      · simp only [Bool.false_eq_true, ↓reduceIte]; apply Fin.ext; dsimp only; omega
      · simp only [↓reduceIte]; apply Fin.ext; dsimp only; omega
    have hl1_simp : path15P1Perm b₁ idx1 =
        (if b₁ j then ⟨2 * j.val, by omega⟩ else ⟨2 * j.val + 1, by omega⟩) := by
      dsimp only [path15P1Perm, Equiv.coe_fn_mk]
      have harg : (⟨idx1.val / 2, by omega⟩ : Fin 7) = j := Fin.ext (by dsimp only; omega)
      rw [harg]
      cases b₁ j
      · simp only [Bool.false_eq_true, ↓reduceIte]; apply Fin.ext; dsimp only; omega
      · simp only [↓reduceIte]; apply Fin.ext; dsimp only; omega
    have hr0_simp : path15P2Perm b₂ idx0 =
        (if h : bitLeft b₂ j = true ∧ 0 < j.val then ⟨2 * j.val - 1, by omega⟩ else ⟨2 * j.val, by omega⟩) := by
      dsimp only [path15P2Perm, Equiv.coe_fn_mk]
      by_cases hj0 : 0 < j.val
      · have h12 : 1 ≤ idx0.val ∧ idx0.val ≤ 12 := ⟨by omega, by omega⟩
        simp only [h12.1, h12.2, and_self, ↓reduceDIte]
        have harg : (⟨(idx0.val - 1) / 2, by omega⟩ : Fin 6) = ⟨j.val - 1, by omega⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [harg]
        have hbit : bitLeft b₂ j = b₂ ⟨j.val - 1, by omega⟩ := by simp [bitLeft, hj0]
        by_cases hb : b₂ ⟨j.val - 1, by omega⟩ = true
        · have hcond : bitLeft b₂ j = true ∧ 0 < j.val := ⟨by rw [hbit, hb], hj0⟩
          simp only [hb, ↓reduceIte, hcond.1, hcond.2, and_self, ↓reduceDIte]
          apply Fin.ext; dsimp only; omega
        · have hcond : ¬ (bitLeft b₂ j = true ∧ 0 < j.val) := fun hc => hb (hbit ▸ hc.1)
          simp only [hb, Bool.false_eq_true, ↓reduceIte, hcond, ↓reduceDIte]
          apply Fin.ext; dsimp only; omega
      · have h12 : ¬ (1 ≤ idx0.val ∧ idx0.val ≤ 12) := by omega
        have hcond : ¬ (bitLeft b₂ j = true ∧ 0 < j.val) := fun hc => hj0 hc.2
        simp only [h12, ↓reduceDIte, hcond]
        apply Fin.ext; dsimp only; omega
    have hr1_simp : path15P2Perm b₂ idx1 =
        (if h : bitRight b₂ j = true ∧ j.val < 6 then ⟨2 * j.val + 2, by omega⟩ else ⟨2 * j.val + 1, by omega⟩) := by
      dsimp only [path15P2Perm, Equiv.coe_fn_mk]
      by_cases hj6 : j.val < 6
      · have h12 : 1 ≤ idx1.val ∧ idx1.val ≤ 12 := ⟨by omega, by omega⟩
        simp only [h12.1, h12.2, and_self, ↓reduceDIte]
        have harg : (⟨(idx1.val - 1) / 2, by omega⟩ : Fin 6) = ⟨j.val, hj6⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [harg]
        have hbit : bitRight b₂ j = b₂ ⟨j.val, hj6⟩ := by simp [bitRight, hj6]
        by_cases hb : b₂ ⟨j.val, hj6⟩ = true
        · have hcond : bitRight b₂ j = true ∧ j.val < 6 := ⟨by rw [hbit, hb], hj6⟩
          simp only [hb, ↓reduceIte, hcond.1, hcond.2, and_self, ↓reduceDIte]
          apply Fin.ext; dsimp only; omega
        · have hcond : ¬ (bitRight b₂ j = true ∧ j.val < 6) := fun hc => hb (hbit ▸ hc.1)
          simp only [hb, Bool.false_eq_true, ↓reduceIte, hcond, ↓reduceDIte]
          apply Fin.ext; dsimp only; omega
      · have h12 : ¬ (1 ≤ idx1.val ∧ idx1.val ≤ 12) := by omega
        have hcond : ¬ (bitRight b₂ j = true ∧ j.val < 6) := fun hc => hj6 hc.2
        simp only [h12, ↓reduceDIte, hcond]
        apply Fin.ext; dsimp only; omega
    simp only [path15P1Equiv, path15P2Equiv, Equiv.coe_fn_mk, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
    rw [hH, hH]
    change H (path15P1Perm b₁ idx0) (path15P2Perm b₂ idx0) *
        H (path15P1Perm b₁ idx1) (path15P2Perm b₂ idx1) = _
    rw [hl_simp, hl1_simp, hr0_simp, hr1_simp]
    cases b₁ j <;> simp
  have hsum_inner : ∀ b₂ : Fin 6 → Bool,
      (∑ b₁ : Fin 7 → Bool, ∏ e : BipEdge pathGraph15 partEvenTrue,
        (starRingEnd ℂ (GI.toC (BGI 0 (path15EdgeEquiv.symm ((path15P1Equiv b₁).1 e)))) *
          GI.toC (BGI 0 (path15EdgeEquiv.symm ((path15P2Equiv b₂).1 e))) +
         starRingEnd ℂ (GI.toC (BGI 1 (path15EdgeEquiv.symm ((path15P1Equiv b₁).1 e)))) *
          GI.toC (BGI 1 (path15EdgeEquiv.symm ((path15P2Equiv b₂).1 e))))) =
      ∏ j : Fin 7, GI.toC (path15BlockGI BGI j (bitLeft b₂ j) (bitRight b₂ j)) := by
    intro b₂
    simp_rw [hprod_b b₂]
    rw [← (Fintype.prod_sum fun j (bj : Bool) =>
      if bj then
        H ⟨2 * j.val + 1, by omega⟩ (if h : bitLeft b₂ j = true ∧ 0 < j.val then ⟨2 * j.val - 1, by omega⟩ else ⟨2 * j.val, by omega⟩) *
        H ⟨2 * j.val, by omega⟩ (if h : bitRight b₂ j = true ∧ j.val < 6 then ⟨2 * j.val + 2, by omega⟩ else ⟨2 * j.val + 1, by omega⟩)
      else
        H ⟨2 * j.val, by omega⟩ (if h : bitLeft b₂ j = true ∧ 0 < j.val then ⟨2 * j.val - 1, by omega⟩ else ⟨2 * j.val, by omega⟩) *
        H ⟨2 * j.val + 1, by omega⟩ (if h : bitRight b₂ j = true ∧ j.val < 6 then ⟨2 * j.val + 2, by omega⟩ else ⟨2 * j.val + 1, by omega⟩))]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sum_bool_ft]
    simp [path15BlockGI, H, GI.toC_add, GI.toC_mul]
  simp_rw [hsum_inner]
  rw [matProdC_eq_sum 6 (path15BlockGI BGI) false false]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  exact (matChain6_eq_prod (fun j x y => GI.toC (path15BlockGI BGI j x y)) b₂).symm

/-- Exact $2 \times 14$ Gaussian-integer spinor matrix giving a negative real part on $LG_{15}$:
`Br = [[5,-2,5,1,5,2,5,0,5,-1,5,0,5,1], [0,4,0,4,1,5,0,5,-1,5,-1,5,2,5]]`,
`Bi = [[0,1,0,2,0,0,0,-2,0,0,0,1,0,0], [0,0,0,0,0,0,1,0,0,0,-1,0,-1,0]]`. -/
def lg15BGI : Fin 2 → Fin 14 → GI
  | 0, 0  => ⟨5, 0⟩   | 0, 1  => ⟨-2, 1⟩ | 0, 2  => ⟨5, 0⟩  | 0, 3  => ⟨1, 2⟩
  | 0, 4  => ⟨5, 0⟩   | 0, 5  => ⟨2, 0⟩  | 0, 6  => ⟨5, 0⟩  | 0, 7  => ⟨0, -2⟩
  | 0, 8  => ⟨5, 0⟩   | 0, 9  => ⟨-1, 0⟩ | 0, 10 => ⟨5, 0⟩  | 0, 11 => ⟨0, 1⟩
  | 0, 12 => ⟨5, 0⟩   | 0, 13 => ⟨1, 0⟩
  | 1, 0  => ⟨0, 0⟩   | 1, 1  => ⟨4, 0⟩  | 1, 2  => ⟨0, 0⟩  | 1, 3  => ⟨4, 0⟩
  | 1, 4  => ⟨1, 0⟩   | 1, 5  => ⟨5, 0⟩  | 1, 6  => ⟨0, 1⟩  | 1, 7  => ⟨5, 0⟩
  | 1, 8  => ⟨-1, 0⟩  | 1, 9  => ⟨5, 0⟩  | 1, 10 => ⟨-1, -1⟩ | 1, 11 => ⟨5, 0⟩
  | 1, 12 => ⟨2, -1⟩  | 1, 13 => ⟨5, 0⟩

theorem cert_lg15_eval :
    matProdGI 6 (path15BlockGI lg15BGI) false false =
      ⟨-40605770611892600000, -1681394136422384600000⟩ := by
  decide

theorem cert_lg15_diag :
    prodFinInt 14 (fun e => hopfNormGI (fun k => lg15BGI k e)) = 58001564658819600000 := by
  decide

theorem lg15BGI_pos_norm : ∀ e : Fin 14, 0 < hopfNormGI (fun k => lg15BGI k e) := by
  decide

/-- Integer 3D vertex coordinates for `pathGraph15` reconstructed recursively via `hopfVecGI`. -/
def lg15PtsIntAux : ℕ → Fin 3 → ℤ
  | 0 => ![0, 0, 0]
  | k + 1 =>
      if h : k < 14 then
        let w := hopfVecGI (fun row => lg15BGI row ⟨k, h⟩)
        let prev := lg15PtsIntAux k
        if k % 2 = 0 then fun j => prev j - w j else fun j => prev j + w j
      else ![0, 0, 0]

def lg15PtsInt (u : Fin 15) : Fin 3 → ℤ := lg15PtsIntAux u.val

theorem lg15Pts_injective : Function.Injective (fun u : Fin 15 => fun j : Fin 3 => (lg15PtsInt u j : ℝ)) := by
  intro u v h
  have hi : lg15PtsInt u = lg15PtsInt v := funext fun j => Int.cast_injective (congrFun h j)
  have hdec : ∀ a b : Fin 15, a ≠ b → lg15PtsInt a ≠ lg15PtsInt b := by decide
  by_contra hne
  exact hdec u v hne hi

/-- Explicit integer 3D configuration `lg15NegConfig : ConfigSpace pathGraph15` with strictly
negative real part ($\approx -0.700081 < 0$). -/
noncomputable def lg15NegConfig : ConfigSpace pathGraph15 :=
  ⟨fun u j => (lg15PtsInt u j : ℝ), fun _ _ hadj h =>
    pathGraph15.ne_of_adj hadj (lg15Pts_injective h)⟩

private lemma lg15Pts_edge_diff (e : Fin 14) (j : Fin 3) :
    (lg15PtsInt (path15Edges e).1.2 j : ℝ) - (lg15PtsInt (path15Edges e).1.1 j : ℝ) =
      (hopfVecGI (fun k => lg15BGI k e) j : ℝ) := by
  have hi : (lg15PtsInt (path15Edges e).1.2 j) - (lg15PtsInt (path15Edges e).1.1 j) =
      hopfVecGI (fun k => lg15BGI k e) j := by
    revert e j; decide
  exact_mod_cast hi

/-- Value of $\mathcal{A}_{LG_{15}}(\mathbf{x})$ at `lg15NegConfig`, shielded as `@[irreducible]`
so `LT.lt` on `ℝ` does not unfold `malkounAmplitude`. -/
@[irreducible] noncomputable def lg15Amp : ℂ :=
  malkounAmplitude pathGraph15 lg15NegConfig

lemma lg15Amp_eq : lg15Amp = malkounAmplitude pathGraph15 lg15NegConfig := by
  unfold lg15Amp; rfl

/-- **Exact Rational Real Part on Malkoun's Linear Path Family $LG_{15}$ (`pathGraph15`):**
$\operatorname{Re}(\mathcal{A}_{LG_{15}}(\mathbf{x})) = -40605770611892600000 / 58001564658819600000$. -/
theorem malkounAmplitude_lg15Neg_re_eq :
    (malkounAmplitude pathGraph15 lg15NegConfig).re =
      (-40605770611892600000 : ℝ) / 58001564658819600000 := by
  let Φ : BipEdge pathGraph15 partEvenTrue → Fin 2 → ℂ :=
    fun e k => GI.toC (lg15BGI k (path15EdgeEquiv.symm e))
  let r : BipEdge pathGraph15 partEvenTrue → ℝ :=
    fun e => (hopfNormGI (fun k => lg15BGI k (path15EdgeEquiv.symm e)) : ℝ)
  have hr_pos : ∀ e, 0 < r e := fun e => Int.cast_pos.mpr (lg15BGI_pos_norm _)
  have hedge_ok : ∀ e,
      ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = r e ∧
      (pauliDot (unitDir (lg15NegConfig.1 e.1.1) (lg15NegConfig.1 e.1.2))).mulVec (Φ e) = Φ e := by
    intro e
    obtain ⟨i, rfl⟩ := path15EdgeEquiv.surjective e
    have hspec := hopfVecGI_spinor_ok (fun k => lg15BGI k i) (lg15BGI_pos_norm i)
      (lg15NegConfig.1 (path15EdgeEquiv i).1.1) (lg15NegConfig.1 (path15EdgeEquiv i).1.2)
      (lg15Pts_edge_diff i)
    have hΦ : Φ (path15EdgeEquiv i) = fun k => GI.toC (lg15BGI k i) :=
      funext fun k => by simp only [Φ, Equiv.symm_apply_apply]
    have hri : r (path15EdgeEquiv i) = (hopfNormGI (fun k => lg15BGI k i) : ℝ) := by
      simp only [r, Equiv.symm_apply_apply]
    rw [hΦ, hri]
    exact ⟨hspec.2.1, hspec.2.2⟩
  rw [malkounAmplitude_bipartite_unnorm pathGraph15 partEvenTrue path15_isBipartite
      lg15NegConfig Φ r hr_pos (fun e => (hedge_ok e).1) (fun e => (hedge_ok e).2)]
  have hsum : (∑ σ₁ : bipP1 pathGraph15 partEvenTrue, ∑ σ₂ : bipP2 pathGraph15 partEvenTrue,
      ∏ e : BipEdge pathGraph15 partEvenTrue,
        (starRingEnd ℂ (Φ (σ₁.1 e) 0) * Φ (σ₂.1 e) 0 +
         starRingEnd ℂ (Φ (σ₁.1 e) 1) * Φ (σ₂.1 e) 1)) =
      GI.toC (matProdGI 6 (path15BlockGI lg15BGI) false false) :=
    path15_gram_sum_eq_toC lg15BGI
  have hden : (∏ e : BipEdge pathGraph15 partEvenTrue, r e) = 58001564658819600000 := by
    rw [← Fintype.prod_equiv path15EdgeEquiv _ _ (fun _ => rfl)]
    have hcast : ∀ m (f : Fin m → ℤ), ((prodFinInt m f : ℤ) : ℝ) = ∏ i : Fin m, (f i : ℝ) := by
      intro m
      induction m with
      | zero => intro f; simp [prodFinInt]
      | succ m ih => intro f; simp only [prodFinInt, Int.cast_mul, Fin.prod_univ_succ, ih]
    have hprod : (∏ i : Fin 14, r (path15EdgeEquiv i)) =
        ((prodFinInt 14 (fun e => hopfNormGI (fun k => lg15BGI k e)) : ℤ) : ℝ) := by
      rw [hcast]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [r, Equiv.symm_apply_apply]
    rw [hprod, cert_lg15_diag]
    norm_num
  rw [hsum, hden, cert_lg15_eval]
  have hre_div : (starRingEnd ℂ (GI.toC ⟨-40605770611892600000, -1681394136422384600000⟩) /
      ((58001564658819600000 : ℝ) : ℂ)).re =
      (-40605770611892600000 : ℝ) / 58001564658819600000 := by
    rw [Complex.div_ofReal_re, Complex.conj_re]
    simp [GI.toC]
  exact hre_div

/-- **Formal Negative Real Part on $LG_{15}$ (`pathGraph15`):** -/
theorem malkounAmplitude_lg15Neg_re_neg : lg15Amp.re < 0 := by
  rw [lg15Amp_eq, malkounAmplitude_lg15Neg_re_eq]
  norm_num

/-- **Formal Negative-Re Disproof on Malkoun's Path Family $LG_n$ ($LG_{15}$):** -/
theorem disproof_malkoun_path_conjecture_C_neg_re :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (_ : DecidableRel T.Adj) (x : ConfigSpace T),
      T.IsTree ∧ (malkounAmplitude T x).re < 0 := by
  refine ⟨15, pathGraph15, instDecidableRelPath15, lg15NegConfig, pathGraph15_isTree, ?_⟩
  rw [← lg15Amp_eq]
  exact malkounAmplitude_lg15Neg_re_neg

end PathGraph15NegRe

end Matematyka.MalkounConjectureC
