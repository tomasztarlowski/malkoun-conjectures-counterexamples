import Mathlib
import Matematyka.Malkoun
import Matematyka.MalkounBipartite
import Matematyka.MalkounCounterexample

/-!
# Malkoun's Conjecture D Disproofs & Unconditional Tree Conjecture C Theorems

We resolve the status of Malkoun's matrix-analytic Conjecture D and bipartite/tree amplitude
conjectures from *Finite graphs and configurations of points* (`arXiv:2508.13472v3`, Section 4):

1. **Disproof of General Conjecture D (`disproof_malkoun_conjecture_D`):**
   We construct an explicit $4 \times 6$ integer matrix $B$ whose unit-free rank-3 Hermitian PSD Gram
   matrix $H = B^H B$ on $E = \mathrm{Fin}\ 6$ (representing the 6-cycle $C_6$) satisfies
   $f_{\sim_1, \sim_2}(H) = 7 < 8 = |P_1 \cap P_2| \prod_{e} H_{ee}$ (ratio $7/8 < 1$).

2. **Disproof of Rank-2 Spinor Conjecture D (`disproof_malkoun_rank2_conjecture_D`):**
   Even when restricted to rank-2 spinor Gram matrices $H = B^H B$ ($B \in M_{2 \times m}(\mathbb{C})$),
   which we show suffice to imply $\operatorname{Re}(\mathcal{A}_G) \ge 1$ for all bipartite graphs
   (`rank2ConjectureD_implies_bipartite_re_ge_one`), Conjecture D fails at $m = 12$ ($C_{12}$) with an
   exact Gaussian-integer $2 \times 12$ matrix giving negative real part
   $-38243634152693760 < 0 < 46450162760601600 = |P_1 \cap P_2| \prod_e H_{ee}$.

3. **Unconditional Conjecture C for Trees & Tree-Restricted Conjecture D:**
   Using general unit-diagonal Hermitian PSD disk bounds (`posSemidef_unitDiag_norm_le_one` and
   `posSemidef_unitDiag_three_disk_bound`), we prove unconditionally for all 3D configurations that
   $\operatorname{Re}(\mathcal{A}_T(\mathbf{x})) \ge 1$, $\|\mathcal{A}_T(\mathbf{x})\| \ge 1$, and
   $\mathcal{A}_T(\mathbf{x}) \neq 0$ for $LG_3$, $LG_4$, $K_{1,3}$ (all trees on $\le 4$ vertices),
   and $LG_5$ (Malkoun Theorem 4.4), and prove `treeConjectureD_implies_conjecture_C` showing that
   Conjecture D restricted to tree edge-incidence partitions implies Conjecture C for all trees.
-/

namespace Matematyka.MalkounConjectureD

open Complex Classical ComplexOrder Matematyka.Malkoun Matematyka.MalkounBipartite
  Matematyka.MalkounCounterexample

private lemma fin2_eq_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

/-! ## Part 1: Even-Cycle Partition Subgroups & Computable Gaussian-Integer Evaluator -/

section EvenCyclePartitions

private def rotFwdNat (m e : ℕ) : ℕ := if e + 1 < m then e + 1 else 0
private def rotBwdNat (m e : ℕ) : ℕ := if e = 0 then m - 1 else e - 1

private lemma rotFwdNat_lt {m e : ℕ} (hm : 0 < m) (_he : e < m) : rotFwdNat m e < m := by
  dsimp [rotFwdNat]; split_ifs <;> omega

private lemma rotBwdNat_lt {m e : ℕ} (hm : 0 < m) (he : e < m) : rotBwdNat m e < m := by
  dsimp [rotBwdNat]; split_ifs <;> omega

private lemma rotBwd_rotFwd {m e : ℕ} (_hm : 0 < m) (he : e < m) :
    rotBwdNat m (rotFwdNat m e) = e := by
  by_cases h : e + 1 < m
  · simp [rotFwdNat, rotBwdNat, h]
  · simp [rotFwdNat, rotBwdNat, h]; omega

private lemma rotFwd_rotBwd {m e : ℕ} (hm : 0 < m) (he : e < m) :
    rotFwdNat m (rotBwdNat m e) = e := by
  by_cases h : e = 0
  · simp [rotFwdNat, rotBwdNat, h]; omega
  · have hlt : e - 1 + 1 < m := by omega
    simp [rotFwdNat, rotBwdNat, h, hlt]; omega

/-- Computable bijection pairing `{2j, 2j+1}` on `Fin (2 * k)`. -/
def pairEquiv (k : ℕ) : Fin k × Bool ≃ Fin (2 * k) where
  toFun
    | (j, false) => ⟨2 * j.val, by omega⟩
    | (j, true) => ⟨2 * j.val + 1, by omega⟩
  invFun e := (⟨e.val / 2, by omega⟩, decide (e.val % 2 = 1))
  left_inv p := by
    rcases p with ⟨⟨j, hj⟩, _ | _⟩
    · apply Prod.ext
      · apply Fin.ext; change (2 * j) / 2 = j; omega
      · change decide ((2 * j) % 2 = 1) = false; exact decide_eq_false (by omega)
    · apply Prod.ext
      · apply Fin.ext; change (2 * j + 1) / 2 = j; omega
      · change decide ((2 * j + 1) % 2 = 1) = true; exact decide_eq_true (by omega)
  right_inv e := by
    rcases e with ⟨e, he⟩
    apply Fin.ext
    dsimp only
    cases h : decide (e % 2 = 1)
    · simp only [decide_eq_false_iff_not] at h; change 2 * (e / 2) = e; omega
    · simp only [decide_eq_true_eq] at h; change 2 * (e / 2) + 1 = e; omega

/-- Cyclic $+1$ shift permutation on `Fin (2 * k)` (`0 ↦ 1 ↦ ... ↦ 2k-1 ↦ 0`). -/
def cycleRot (k : ℕ) [NeZero k] : Equiv.Perm (Fin (2 * k)) where
  toFun e := ⟨rotFwdNat (2 * k) e.val, rotFwdNat_lt (by have := NeZero.pos k; omega) e.isLt⟩
  invFun e := ⟨rotBwdNat (2 * k) e.val, rotBwdNat_lt (by have := NeZero.pos k; omega) e.isLt⟩
  left_inv e := Fin.ext (rotBwd_rotFwd (by have := NeZero.pos k; omega) e.isLt)
  right_inv e := Fin.ext (rotFwd_rotBwd (by have := NeZero.pos k; omega) e.isLt)

/-- First even-cycle edge partition: pairs `{2j, 2j+1}`. -/
def cycleKappa1 (k : ℕ) (e : Fin (2 * k)) : Fin k :=
  ((pairEquiv k).symm e).1

/-- Shifted even-cycle edge partition: pairs `{2j+1, 2j+2 mod 2k}`. -/
def cycleKappa2 (k : ℕ) [NeZero k] (e : Fin (2 * k)) : Fin k :=
  cycleKappa1 k (cycleRot k e)

private lemma xor_xor_cancel (x y : Bool) : Bool.xor (Bool.xor x y) y = x := by
  cases x <;> cases y <;> rfl

/-- Involution swapping `{2j, 2j+1}` iff `b j = true`. -/
def cyclePerm1 (k : ℕ) (b : Fin k → Bool) : Equiv.Perm (Fin (2 * k)) where
  toFun e :=
    let p := (pairEquiv k).symm e
    pairEquiv k (p.1, Bool.xor p.2 (b p.1))
  invFun e :=
    let p := (pairEquiv k).symm e
    pairEquiv k (p.1, Bool.xor p.2 (b p.1))
  left_inv e := by
    dsimp only
    rw [(pairEquiv k).symm_apply_apply]
    simp only [xor_xor_cancel]
    exact (pairEquiv k).apply_symm_apply e
  right_inv e := by
    dsimp only
    rw [(pairEquiv k).symm_apply_apply]
    simp only [xor_xor_cancel]
    exact (pairEquiv k).apply_symm_apply e

private lemma cyclePerm1_pair_false (k : ℕ) (b : Fin k → Bool) (j : Fin k) :
    cyclePerm1 k b (pairEquiv k (j, false)) = pairEquiv k (j, b j) := by
  dsimp only [cyclePerm1, Equiv.coe_fn_mk]
  rw [(pairEquiv k).symm_apply_apply]
  cases b j <;> rfl

private lemma cyclePerm1_pair_true (k : ℕ) (b : Fin k → Bool) (j : Fin k) :
    cyclePerm1 k b (pairEquiv k (j, true)) = pairEquiv k (j, !(b j)) := by
  dsimp only [cyclePerm1, Equiv.coe_fn_mk]
  rw [(pairEquiv k).symm_apply_apply]
  cases b j <;> rfl

private lemma cycleKappa1_val (k : ℕ) (e : Fin (2 * k)) : (cycleKappa1 k e).val = e.val / 2 := rfl

private lemma pairEquiv_false_val (k : ℕ) (j : Fin k) :
    (pairEquiv k (j, false)).val = 2 * j.val := rfl

private lemma pairEquiv_true_val (k : ℕ) (j : Fin k) :
    (pairEquiv k (j, true)).val = 2 * j.val + 1 := rfl

/-- Computable equivalence `(Fin k → Bool) ≃ partitionSubgroup (cycleKappa1 k)`. -/
def cycleP1Equiv (k : ℕ) : (Fin k → Bool) ≃ partitionSubgroup (cycleKappa1 k) where
  toFun b := ⟨cyclePerm1 k b, fun e => by
    change ((pairEquiv k).symm (pairEquiv k (((pairEquiv k).symm e).1, _))).1 =
      ((pairEquiv k).symm e).1
    rw [(pairEquiv k).symm_apply_apply]⟩
  invFun σ := fun j => decide ((σ.1 (pairEquiv k (j, false))).val ≠ 2 * j.val)
  left_inv b := by
    funext j
    simp only [cyclePerm1_pair_false]
    cases h : b j
    · rw [pairEquiv_false_val]; exact decide_eq_false (not_not.mpr rfl)
    · rw [pairEquiv_true_val]; exact decide_eq_true (by omega)
  right_inv σ := by
    apply Subtype.ext
    ext e
    dsimp only
    let j : Fin k := cycleKappa1 k e
    let e0 := pairEquiv k (j, false)
    let e1 := pairEquiv k (j, true)
    have h0' : cycleKappa1 k (σ.1 e0) = cycleKappa1 k e0 := σ.2 e0
    have h1' : cycleKappa1 k (σ.1 e1) = cycleKappa1 k e1 := σ.2 e1
    have hj0 : (σ.1 e0).val / 2 = j.val := by
      have hv := congrArg Fin.val h0'
      rw [cycleKappa1_val, cycleKappa1_val, pairEquiv_false_val] at hv
      omega
    have hj1 : (σ.1 e1).val / 2 = j.val := by
      have hv := congrArg Fin.val h1'
      rw [cycleKappa1_val, cycleKappa1_val, pairEquiv_true_val] at hv
      omega
    have hne : e0 ≠ e1 := fun h => by
      have hv := congrArg Fin.val h
      rw [pairEquiv_false_val, pairEquiv_true_val] at hv
      omega
    have hne_val : (σ.1 e0).val ≠ (σ.1 e1).val := fun h => hne (σ.1.injective (Fin.ext h))
    have hcases : e = e0 ∨ e = e1 := by
      rcases e with ⟨ev, hev⟩
      by_cases hmod : ev % 2 = 0
      · left; apply Fin.ext
        change ev = 2 * (ev / 2)
        omega
      · right; apply Fin.ext
        change ev = 2 * (ev / 2) + 1
        omega
    by_cases hb : (σ.1 e0).val = 2 * j.val
    · have hc : decide ((σ.1 e0).val ≠ 2 * j.val) = false := decide_eq_false (not_not.mpr hb)
      rcases hcases with he | he
      · rw [he]
        change (cyclePerm1 k _ (pairEquiv k (j, false))).val = (σ.1 e0).val
        rw [cyclePerm1_pair_false, hc, pairEquiv_false_val]
        exact hb.symm
      · rw [he]
        change (cyclePerm1 k _ (pairEquiv k (j, true))).val = (σ.1 e1).val
        rw [cyclePerm1_pair_true, hc]
        simp only [Bool.not_false]
        rw [pairEquiv_true_val]
        omega
    · have hc : decide ((σ.1 e0).val ≠ 2 * j.val) = true := decide_eq_true hb
      rcases hcases with he | he
      · rw [he]
        change (cyclePerm1 k _ (pairEquiv k (j, false))).val = (σ.1 e0).val
        rw [cyclePerm1_pair_false, hc, pairEquiv_true_val]
        omega
      · rw [he]
        change (cyclePerm1 k _ (pairEquiv k (j, true))).val = (σ.1 e1).val
        rw [cyclePerm1_pair_true, hc]
        simp only [Bool.not_true]
        rw [pairEquiv_false_val]
        omega

/-- Computable equivalence `(Fin k → Bool) ≃ partitionSubgroup (cycleKappa2 k)` obtained by conjugation. -/
def cycleP2Equiv (k : ℕ) [NeZero k] : (Fin k → Bool) ≃ partitionSubgroup (cycleKappa2 k) where
  toFun b := ⟨(cycleRot k)⁻¹ * (cyclePerm1 k b) * cycleRot k, fun e => by
    change cycleKappa1 k (cycleRot k (((cycleRot k)⁻¹ * cyclePerm1 k b * cycleRot k) e)) =
      cycleKappa1 k (cycleRot k e)
    have hid : cycleRot k ((cycleRot k)⁻¹ (cyclePerm1 k b (cycleRot k e))) =
        cyclePerm1 k b (cycleRot k e) := by
      simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    simp only [Equiv.Perm.mul_apply, hid]
    exact (cycleP1Equiv k b).2 (cycleRot k e)⟩
  invFun τ := (cycleP1Equiv k).symm ⟨cycleRot k * τ.1 * (cycleRot k)⁻¹, fun e => by
    simp only [Equiv.Perm.mul_apply, cycleKappa1]
    have ht := τ.2 ((cycleRot k)⁻¹ e)
    change cycleKappa1 k (cycleRot k (τ.1 ((cycleRot k)⁻¹ e))) =
      cycleKappa1 k (cycleRot k ((cycleRot k)⁻¹ e)) at ht
    have hinv : cycleRot k ((cycleRot k)⁻¹ e) = e := by
      simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    simpa only [cycleKappa1, hinv] using ht⟩
  left_inv b := by
    have hin : cycleRot k * ((cycleRot k)⁻¹ * cyclePerm1 k b * cycleRot k) * (cycleRot k)⁻¹ =
        cyclePerm1 k b := by group
    change (cycleP1Equiv k).symm ⟨_, _⟩ = b
    rw [(cycleP1Equiv k).symm_apply_eq]
    exact Subtype.ext hin
  right_inv τ := by
    apply Subtype.ext
    have hin : ∀ e, cycleKappa1 k ((cycleRot k * τ.1 * (cycleRot k)⁻¹) e) = cycleKappa1 k e := by
      intro e
      simp only [Equiv.Perm.mul_apply]
      have ht := τ.2 ((cycleRot k)⁻¹ e)
      change cycleKappa1 k (cycleRot k (τ.1 ((cycleRot k)⁻¹ e))) =
        cycleKappa1 k (cycleRot k ((cycleRot k)⁻¹ e)) at ht
      have hinv : cycleRot k ((cycleRot k)⁻¹ e) = e := by
        simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      rwa [hinv] at ht
    have h := congrArg Subtype.val
      ((cycleP1Equiv k).apply_symm_apply ⟨cycleRot k * τ.1 * (cycleRot k)⁻¹, hin⟩)
    dsimp only [cycleP1Equiv, Equiv.coe_fn_mk] at h ⊢
    change (cycleRot k)⁻¹ * (cyclePerm1 k _) * cycleRot k = τ.1
    rw [h]
    group

/-- For $k \ge 2$, the even-cycle partitions share only the identity: $|P_1 \cap P_2| = 1$. -/
theorem card_cycleP1_inf_cycleP2 (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    [Fintype ↥(partitionSubgroup (cycleKappa1 k) ⊓ partitionSubgroup (cycleKappa2 k))] :
    Fintype.card ↥(partitionSubgroup (cycleKappa1 k) ⊓ partitionSubgroup (cycleKappa2 k)) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, fun ⟨σ, h1, h2⟩ => Subtype.ext ?_⟩
  let b := (cycleP1Equiv k).symm ⟨σ, h1⟩
  have hσ : σ = cyclePerm1 k b :=
    (congrArg Subtype.val ((cycleP1Equiv k).apply_symm_apply ⟨σ, h1⟩)).symm
  have hb : ∀ j : Fin k, b j = false := by
    intro j
    by_contra hbj
    have hbt : b j = true := Bool.eq_true_of_not_eq_false hbj
    have hmem := h2 (pairEquiv k (j, false))
    have hstep : σ (pairEquiv k (j, false)) = pairEquiv k (j, true) := by
      rw [hσ, cyclePerm1_pair_false, hbt]
    rw [hstep] at hmem
    have hval := congrArg Fin.val hmem
    change (cycleRot k (pairEquiv k (j, true))).val / 2 =
        (cycleRot k (pairEquiv k (j, false))).val / 2 at hval
    dsimp only [cycleRot, Equiv.coe_fn_mk] at hval
    rw [pairEquiv_false_val, pairEquiv_true_val] at hval
    dsimp only [rotFwdNat] at hval
    split_ifs at hval <;> omega
  apply Equiv.ext
  intro e
  change σ e = (1 : Equiv.Perm (Fin (2 * k))) e
  rw [hσ]
  apply Fin.ext
  change (cyclePerm1 k b e).val = e.val
  dsimp only [cyclePerm1, Equiv.coe_fn_mk]
  rw [hb, Bool.xor_false, (pairEquiv k).apply_symm_apply]

/-- Gaussian-integer complex conjugate. -/
def starGI (z : GI) : GI := ⟨z.re, -z.im⟩

private lemma toC_starGI (z : GI) : GI.toC (starGI z) = starRingEnd ℂ (GI.toC z) := by
  simp only [starGI, GI.toC, map_add, map_mul, Complex.conj_I, map_intCast, Int.cast_neg]
  ring

/-- Computable finite sum over `Fin m` for `GI`. -/
def sumFinGI : ∀ m : ℕ, (Fin m → GI) → GI
  | 0, _ => 0
  | m + 1, f => f 0 + sumFinGI m (fun i => f i.succ)

/-- Computable finite product over `Fin m` for `GI`. -/
def prodFinGI : ∀ m : ℕ, (Fin m → GI) → GI
  | 0, _ => 1
  | m + 1, f => f 0 * prodFinGI m (fun i => f i.succ)

/-- Computable finite product over `Fin m` for `ℤ`. -/
def prodFinInt : ∀ m : ℕ, (Fin m → ℤ) → ℤ
  | 0, _ => 1
  | m + 1, f => f 0 * prodFinInt m (fun i => f i.succ)

/-- Computable sum over `Fin m → Bool` for `GI`. -/
def sumBoolVecGI : ∀ m : ℕ, ((Fin m → Bool) → GI) → GI
  | 0, f => f Fin.elim0
  | m + 1, f => sumBoolVecGI m (fun b => f (Fin.cons false b)) + sumBoolVecGI m (fun b => f (Fin.cons true b))

private lemma toC_sumFinGI : ∀ (m : ℕ) (f : Fin m → GI),
    GI.toC (sumFinGI m f) = ∑ i : Fin m, GI.toC (f i)
  | 0, _ => by simp [sumFinGI]
  | m + 1, f => by
      simp only [sumFinGI, GI.toC_add, Fin.sum_univ_succ, toC_sumFinGI m]

private lemma toC_prodFinGI : ∀ (m : ℕ) (f : Fin m → GI),
    GI.toC (prodFinGI m f) = ∏ i : Fin m, GI.toC (f i)
  | 0, _ => by simp [prodFinGI]
  | m + 1, f => by
      simp only [prodFinGI, GI.toC_mul, Fin.prod_univ_succ, toC_prodFinGI m]

private lemma prodFinInt_cast (m : ℕ) (f : Fin m → ℤ) :
    ((prodFinInt m f : ℤ) : ℝ) = ∏ i : Fin m, (f i : ℝ) := by
  induction m with
  | zero => simp [prodFinInt]
  | succ m ih =>
      simp only [prodFinInt, Int.cast_mul, Fin.prod_univ_succ]
      rw [ih]

private lemma sum_bool_false_true (g : Bool → ℂ) : (∑ b : Bool, g b) = g false + g true := by
  rw [Fintype.sum_bool]
  ring

private lemma prod_bool_false_true (g : Bool → ℂ) : (∏ b : Bool, g b) = g false * g true := by
  rw [Fintype.prod_bool]
  ring

private lemma sumBoolVecGI_toC : ∀ (m : ℕ) (f : (Fin m → Bool) → GI),
    GI.toC (sumBoolVecGI m f) = ∑ b : Fin m → Bool, GI.toC (f b)
  | 0, f => by
      simp only [sumBoolVecGI]
      rw [Fintype.sum_unique]
      exact congrArg (fun g => GI.toC (f g)) (Subsingleton.elim Fin.elim0 _)
  | m + 1, f => by
      simp only [sumBoolVecGI, GI.toC_add, sumBoolVecGI_toC m]
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Bool))
        (fun p => GI.toC (f (Fin.cons p.1 p.2))) (fun b => GI.toC (f b)) (fun _ => rfl)]
      rw [Fintype.sum_prod_type, sum_bool_false_true]

/-- Entry `(a, b)` of $H = B^H B$ computed in exact `GI`. -/
def gramGI (r k : ℕ) (BGI : Fin r → Fin (2 * k) → GI) (a b : Fin (2 * k)) : GI :=
  sumFinGI r fun i => starGI (BGI i a) * BGI i b

private lemma toC_gramGI (r k : ℕ) (BGI : Fin r → Fin (2 * k) → GI) (a b : Fin (2 * k)) :
    GI.toC (gramGI r k BGI a b) =
      ((Matrix.of (fun i e => GI.toC (BGI i e))).conjTranspose *
       Matrix.of (fun i e => GI.toC (BGI i e))) a b := by
  simp only [gramGI, toC_sumFinGI, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Complex.star_def, GI.toC_mul, toC_starGI]

/-- Computable `GI` evaluator for $f_{\sim_1, \sim_2}(B^H B)$ on the $2k$-cycle (sum over $b_2$, product over $j$). -/
def cycleEvalGI (r k : ℕ) [NeZero k] (BGI : Fin r → Fin (2 * k) → GI) : GI :=
  sumBoolVecGI k fun b₂ =>
    prodFinGI k fun j =>
      let e0 := pairEquiv k (j, false)
      let e1 := pairEquiv k (j, true)
      let t0 := (cycleP2Equiv k b₂).1 e0
      let t1 := (cycleP2Equiv k b₂).1 e1
      gramGI r k BGI e0 t0 * gramGI r k BGI e1 t1 +
      gramGI r k BGI e1 t0 * gramGI r k BGI e0 t1

private lemma sum_prod_fin_bool (m : ℕ) (F : Fin m → Bool → ℂ) :
    (∑ b : Fin m → Bool, ∏ j : Fin m, F j (b j)) = ∏ j : Fin m, (F j false + F j true) := by
  exact (Fintype.prod_sum F).symm.trans <| Finset.prod_congr rfl fun j _ => sum_bool_false_true (F j)

/-- Exact identity between the full $2^k \times 2^k$ Gram sum on `Fin (2 * k)` and `GI.toC (cycleEvalGI ...)`. -/
theorem cycle_gram_sum_eq_toC (r k : ℕ) [NeZero k] (BGI : Fin r → Fin (2 * k) → GI) :
    let B : Matrix (Fin r) (Fin (2 * k)) ℂ := fun i e => GI.toC (BGI i e)
    let H := B.conjTranspose * B
    (∑ σ₁ : partitionSubgroup (cycleKappa1 k), ∑ σ₂ : partitionSubgroup (cycleKappa2 k),
      ∏ e : Fin (2 * k), H (σ₁.1 e) (σ₂.1 e)) = GI.toC (cycleEvalGI r k BGI) := by
  intro B H
  have hH : ∀ a b, H a b = GI.toC (gramGI r k BGI a b) := fun a b => (toC_gramGI r k BGI a b).symm
  rw [← Fintype.sum_equiv (cycleP1Equiv k) _ _ (fun _ => rfl)]
  rw [Finset.sum_comm]
  rw [← Fintype.sum_equiv (cycleP2Equiv k) _ _ (fun _ => rfl)]
  rw [cycleEvalGI, sumBoolVecGI_toC]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [toC_prodFinGI]
  let F : Fin k → Bool → ℂ := fun j b =>
    let e0 := pairEquiv k (j, false)
    let e1 := pairEquiv k (j, true)
    let t0 := (cycleP2Equiv k b₂).1 e0
    let t1 := (cycleP2Equiv k b₂).1 e1
    GI.toC (if b = false then gramGI r k BGI e0 t0 * gramGI r k BGI e1 t1
            else gramGI r k BGI e1 t0 * gramGI r k BGI e0 t1)
  have hterm : ∀ b₁ : Fin k → Bool,
      (∏ e : Fin (2 * k), H ((cycleP1Equiv k b₁).1 e) ((cycleP2Equiv k b₂).1 e)) =
      ∏ j : Fin k, F j (b₁ j) := by
    intro b₁
    rw [← Fintype.prod_equiv (pairEquiv k)
      (fun p => H ((cycleP1Equiv k b₁).1 (pairEquiv k p)) ((cycleP2Equiv k b₂).1 (pairEquiv k p)))
      (fun e => H ((cycleP1Equiv k b₁).1 e) ((cycleP2Equiv k b₂).1 e)) (fun _ => rfl)]
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [prod_bool_false_true]
    change H (cyclePerm1 k b₁ (pairEquiv k (j, false))) ((cycleP2Equiv k b₂).1 (pairEquiv k (j, false))) *
        H (cyclePerm1 k b₁ (pairEquiv k (j, true))) ((cycleP2Equiv k b₂).1 (pairEquiv k (j, true))) = _
    rw [cyclePerm1_pair_false, cyclePerm1_pair_true]
    dsimp only [F]
    cases hb : b₁ j <;> simp [hH, GI.toC_mul]
  simp_rw [hterm]
  rw [sum_prod_fin_bool k F]
  refine Finset.prod_congr rfl fun j _ => ?_
  dsimp only [F]
  simp [GI.toC_add]

end EvenCyclePartitions

/-! ## Part 2: Disproofs of General Conjecture D ($C_6$) and Rank-2 Spinor Conjecture D ($C_{12}$) -/

section DisproofConjectureD

/-- Exact $4 \times 6$ integer matrix (rank 3) whose Gram matrix $H = B^H B$ refutes general Conjecture D at $m=6$. -/
def c6BGI : Fin 4 → Fin 6 → GI
  | 0, 0 => GI.ofInt 1 | 0, 1 => GI.ofInt 0 | 0, 2 => GI.ofInt 1 | 0, 3 => GI.ofInt 0 | 0, 4 => GI.ofInt 1 | 0, 5 => GI.ofInt 0
  | 1, 0 => GI.ofInt 0 | 1, 1 => GI.ofInt 1 | 1, 2 => GI.ofInt 0 | 1, 3 => GI.ofInt 0 | 1, 4 => GI.ofInt 0 | 1, 5 => GI.ofInt (-1)
  | 2, 0 => GI.ofInt 0 | 2, 1 => GI.ofInt (-1) | 2, 2 => GI.ofInt 0 | 2, 3 => GI.ofInt 1 | 2, 4 => GI.ofInt 0 | 2, 5 => GI.ofInt 0
  | 3, 0 => GI.ofInt 0 | 3, 1 => GI.ofInt 0 | 3, 2 => GI.ofInt 0 | 3, 3 => GI.ofInt (-1) | 3, 4 => GI.ofInt 0 | 3, 5 => GI.ofInt 1

theorem cert_c6_eval : cycleEvalGI 4 3 c6BGI = ⟨7, 0⟩ := by decide
theorem cert_c6_diag : prodFinInt 6 (fun e => (gramGI 4 3 c6BGI e e).re) = 8 := by decide

/-- **Formal Disproof of Malkoun's Conjecture D (`arXiv:2508.13472v3`, Section 4):**
On $E = \mathrm{Fin}\ 6$ with $6$-cycle partitions `cycleKappa1 3` and `cycleKappa2 3`, the rank-3
integer Gram matrix `c6Bᴴ * c6B` satisfies $f_{\sim_1, \sim_2}(H) = 7 < 8 = |P_1 \cap P_2| \prod_e \operatorname{Re}(H_{ee})$. -/
theorem disproof_malkoun_conjecture_D : ¬ MalkounConjectureDProp := by
  intro hD
  let B : Matrix (Fin 4) (Fin 6) ℂ := fun i e => GI.toC (c6BGI i e)
  let H := B.conjTranspose * B
  have hpsd : H.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have hineq := hD (Fin 6) (Fin 3) (Fin 3) (cycleKappa1 3) (cycleKappa2 3) H hpsd
  have hsum : (∑ σ₁ : partitionSubgroup (cycleKappa1 3), ∑ σ₂ : partitionSubgroup (cycleKappa2 3),
      ∏ e : Fin 6, H (σ₁.1 e) (σ₂.1 e)).re = 7 := by
    rw [cycle_gram_sum_eq_toC 4 3 c6BGI, cert_c6_eval]
    simp [GI.toC]
  have hcard : ∀ [inst : Fintype ↥(partitionSubgroup (cycleKappa1 3) ⊓ partitionSubgroup (cycleKappa2 3))],
      @Fintype.card ↥(partitionSubgroup (cycleKappa1 3) ⊓ partitionSubgroup (cycleKappa2 3)) inst = 1 :=
    fun {_} => card_cycleP1_inf_cycleP2 3 (by norm_num)
  have hdiag : (∏ e : Fin 6, (H e e).re) = 8 := by
    have heq : (fun e : Fin 6 => (H e e).re) = fun e => ((gramGI 4 3 c6BGI e e).re : ℝ) := by
      ext e
      have hg : H e e = GI.toC (gramGI 4 3 c6BGI e e) := (toC_gramGI 4 3 c6BGI e e).symm
      rw [hg]
      simp [GI.toC]
    rw [heq, ← prodFinInt_cast 6, cert_c6_diag]
    norm_num
  rw [hsum, hcard, hdiag] at hineq
  norm_num at hineq

/-- **Rank-2 Spinor Conjecture D:** Conjecture D restricted to rank-2 Gram matrices $H = B^H B$
($B \in M_{2 \times |E|}(\mathbb{C})$). -/
def MalkounRank2ConjectureDProp : Prop :=
  ∀ (E V₁ V₂ : Type) [Fintype E] [DecidableEq E] (κ₁ : E → V₁) (κ₂ : E → V₂)
    (B : Matrix (Fin 2) E ℂ),
    let H := B.conjTranspose * B
    (∑ σ₁ : partitionSubgroup κ₁, ∑ σ₂ : partitionSubgroup κ₂,
      ∏ e : E, H (σ₁.1 e) (σ₂.1 e)).re ≥
      (Fintype.card ↥(partitionSubgroup κ₁ ⊓ partitionSubgroup κ₂) : ℝ) *
        ∏ e : E, (H e e).re

private lemma matrix_fin2_conjMul_apply {E : Type*} (B : Matrix (Fin 2) E ℂ) (a b : E) :
    (B.conjTranspose * B) a b =
      starRingEnd ℂ (B 0 a) * B 0 b + starRingEnd ℂ (B 1 a) * B 1 b := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- Even Rank-2 Spinor Conjecture D suffices to imply $\operatorname{Re}(\mathcal{A}_G) \ge 1$ for
every finite simple bipartite graph $G$. -/
theorem rank2ConjectureD_implies_bipartite_re_ge_one (hR2 : MalkounRank2ConjectureDProp)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (part : Fin n → Bool) (hb : IsBipartite G part) (x : ConfigSpace G) :
    1 ≤ (malkounAmplitude G x).re := by
  rw [malkounAmplitude_bipartite_eq_conj_gram G part hb x, Complex.conj_re]
  let B : Matrix (Fin 2) (BipEdge G part) ℂ := fun k e => bipEdgeSpinor x e k
  have hB : B.conjTranspose * B = bipGramMatrix G part x := by
    ext a b
    exact matrix_fin2_conjMul_apply B a b
  have hineq := hR2 (BipEdge G part) (Fin n) (Fin n) (fun e => e.1.1) (fun e => e.1.2) B
  dsimp only at hineq
  rw [hB] at hineq
  have hcard : ∀ [inst : Fintype ↥(bipP1 G part ⊓ bipP2 G part)],
      @Fintype.card ↥(bipP1 G part ⊓ bipP2 G part) inst = 1 := by
    intro inst
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subgroup.one_mem _⟩, fun y => Subtype.ext ?_⟩
    exact Subgroup.mem_bot.mp ((bipP1_inf_bipP2_eq_bot G part) ▸ y.2)
  have hdiag : ∀ e : BipEdge G part, (bipGramMatrix G part x e e).re = 1 := fun e => by
    rw [bipGramMatrix_diag_eq_one, Complex.one_re]
  rw [show partitionSubgroup (fun e : BipEdge G part => e.1.1) = bipP1 G part from rfl,
      show partitionSubgroup (fun e : BipEdge G part => e.1.2) = bipP2 G part from rfl] at hineq
  rw [hcard, Nat.cast_one, one_mul, Finset.prod_eq_one (fun e _ => hdiag e)] at hineq
  exact hineq

/-- Exact $2 \times 12$ Gaussian-integer matrix refuting Rank-2 Spinor Conjecture D on $C_{12}$
with negative real part $-38243634152693760 < 0$. -/
def c12BGI : Fin 2 → Fin 12 → GI
  | 0, 0 => ⟨3, 3⟩   | 0, 1 => ⟨0, -2⟩  | 0, 2 => ⟨3, 2⟩   | 0, 3 => ⟨-1, 1⟩
  | 0, 4 => ⟨0, 4⟩   | 0, 5 => ⟨0, 2⟩   | 0, 6 => ⟨-4, -2⟩ | 0, 7 => ⟨3, -2⟩
  | 0, 8 => ⟨-2, 4⟩  | 0, 9 => ⟨-3, -1⟩ | 0, 10 => ⟨2, 4⟩  | 0, 11 => ⟨3, -2⟩
  | 1, 0 => ⟨-3, 0⟩  | 1, 1 => ⟨2, -4⟩  | 1, 2 => ⟨-3, -1⟩ | 1, 3 => ⟨-3, 4⟩
  | 1, 4 => ⟨1, -3⟩  | 1, 5 => ⟨1, 4⟩   | 1, 6 => ⟨2, 2⟩   | 1, 7 => ⟨2, -3⟩
  | 1, 8 => ⟨1, -1⟩  | 1, 9 => ⟨-3, -1⟩ | 1, 10 => ⟨-1, -1⟩ | 1, 11 => ⟨4, -1⟩

theorem cert_c12_eval :
    cycleEvalGI 2 6 c12BGI = ⟨-38243634152693760, -1338124499804113920⟩ := by decide

theorem cert_c12_diag :
    prodFinInt 12 (fun e => (gramGI 2 6 c12BGI e e).re) = 46450162760601600 := by decide

/-- **Formal Disproof of Rank-2 Spinor Conjecture D:**
On $E = \mathrm{Fin}\ 12$ ($C_{12}$ partitions), `c12Bᴴ * c12B` gives negative real part
$-38243634152693760 < 0 < 46450162760601600$. -/
theorem disproof_malkoun_rank2_conjecture_D : ¬ MalkounRank2ConjectureDProp := by
  intro hR2
  let B : Matrix (Fin 2) (Fin 12) ℂ := fun i e => GI.toC (c12BGI i e)
  let H := B.conjTranspose * B
  have hineq := hR2 (Fin 12) (Fin 6) (Fin 6) (cycleKappa1 6) (cycleKappa2 6) B
  dsimp only at hineq
  have hsum : (∑ σ₁ : partitionSubgroup (cycleKappa1 6), ∑ σ₂ : partitionSubgroup (cycleKappa2 6),
      ∏ e : Fin 12, H (σ₁.1 e) (σ₂.1 e)).re = -38243634152693760 := by
    rw [cycle_gram_sum_eq_toC 2 6 c12BGI, cert_c12_eval]
    simp [GI.toC]
  have hcard : ∀ [inst : Fintype ↥(partitionSubgroup (cycleKappa1 6) ⊓ partitionSubgroup (cycleKappa2 6))],
      @Fintype.card ↥(partitionSubgroup (cycleKappa1 6) ⊓ partitionSubgroup (cycleKappa2 6)) inst = 1 :=
    fun {_} => card_cycleP1_inf_cycleP2 6 (by norm_num)
  have hdiag : (∏ e : Fin 12, (H e e).re) = 46450162760601600 := by
    have heq : (fun e : Fin 12 => (H e e).re) = fun e => ((gramGI 2 6 c12BGI e e).re : ℝ) := by
      ext e
      have hg : H e e = GI.toC (gramGI 2 6 c12BGI e e) := (toC_gramGI 2 6 c12BGI e e).symm
      rw [hg]
      simp [GI.toC]
    rw [heq, ← prodFinInt_cast 12, cert_c12_diag]
    norm_num
  rw [hsum, hcard, hdiag] at hineq
  norm_num at hineq

end DisproofConjectureD

/-! ## Part 3: Unconditional PSD Bounds, Conjecture C for $LG_3, LG_4, K_{1,3}, LG_5$, and Tree Frontier -/

section TreePositivity

private lemma norm_sq_eq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma conj_mul_eq_norm_sq (z : ℂ) : starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, ← norm_sq_eq_mul_conj]

private lemma re_conj_eq_re (z : ℂ) : (starRingEnd ℂ z).re = z.re := by simp

private lemma norm_add_sq_identity (c d : ℂ) :
    ‖c + d‖ ^ 2 = ‖c‖ ^ 2 + 2 * (d * starRingEnd ℂ c).re + ‖d‖ ^ 2 := by
  have hc : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hd : ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hcd : ‖c + d‖ ^ 2 = (c + d).re ^ 2 + (c + d).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hc, hd, hcd]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma two_mul_sqrt_am_gm' (u v : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    2 * (u * v * Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2))) ≤ u ^ 2 + v ^ 2 - 2 * u ^ 2 * v ^ 2 := by
  have h1u : 0 ≤ 1 - u ^ 2 := by nlinarith
  have h1v : 0 ≤ 1 - v ^ 2 := by nlinarith
  rw [Real.sqrt_mul h1u]
  have hsq : 0 ≤ (u * Real.sqrt (1 - v ^ 2) - v * Real.sqrt (1 - u ^ 2)) ^ 2 := sq_nonneg _
  have hru : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt h1u
  have hrv : Real.sqrt (1 - v ^ 2) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt h1v
  nlinarith

/-- Any entry of a unit-diagonal Hermitian PSD matrix satisfies `‖H i j‖ ≤ 1`. -/
theorem posSemidef_unitDiag_norm_le_one {E : Type*} (H : Matrix E E ℂ)
    (hH : H.PosSemidef) (hdiag : ∀ e, H e e = 1) (i j : E) :
    ‖H i j‖ ≤ 1 := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := H.submatrix ![i, j] ![i, j]
  have hM : M.PosSemidef := hH.submatrix ![i, j]
  have hherm : M.IsHermitian := hM.isHermitian
  have hm00 : M 0 0 = 1 := hdiag i
  have hm11 : M 1 1 = 1 := hdiag j
  have hm10 : M 1 0 = starRingEnd ℂ (M 0 1) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 1) 0).symm
  let v : Fin 2 → ℂ := ![-M 0 1, 1]
  have hquad := (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg v)).1
  rw [Complex.zero_re] at hquad
  have hval : (star v ⬝ᵥ M.mulVec v) = ((1 - ‖M 0 1‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
      v, Matrix.cons_val_zero, Matrix.cons_val_one, hm00, hm11, hm10, map_neg, map_one]
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    linear_combination -(conj_mul_eq_norm_sq (M 0 1))
  rw [hval, Complex.ofReal_re] at hquad
  have hsq : ‖M 0 1‖ ^ 2 ≤ 1 := by linarith
  have hnorm : ‖M 0 1‖ ≤ 1 := by nlinarith [norm_nonneg (M 0 1)]
  simpa [M] using hnorm

/-- Any three indices of a unit-diagonal Hermitian PSD matrix satisfy Malkoun's $3 \times 3$ disk bound:
$\|H_{ik} - H_{ij} H_{jk}\| \le \sqrt{(1 - \|H_{ij}\|^2)(1 - \|H_{jk}\|^2)}$. -/
theorem posSemidef_unitDiag_three_disk_bound {E : Type*} (H : Matrix E E ℂ)
    (hH : H.PosSemidef) (hdiag : ∀ e, H e e = 1) (i j k : E) :
    ‖H i k - H i j * H j k‖ ≤ Real.sqrt ((1 - ‖H i j‖ ^ 2) * (1 - ‖H j k‖ ^ 2)) := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := H.submatrix ![i, j, k] ![i, j, k]
  have hM : M.PosSemidef := hH.submatrix ![i, j, k]
  have hherm : M.IsHermitian := hM.isHermitian
  let a := M 0 1
  let b := M 1 2
  let c := M 0 2
  have ha1 : ‖a‖ ≤ 1 := posSemidef_unitDiag_norm_le_one H hH hdiag i j
  have hm00 : M 0 0 = 1 := hdiag i
  have hm11 : M 1 1 = 1 := hdiag j
  have hm22 : M 2 2 = 1 := hdiag k
  have hm10 : M 1 0 = starRingEnd ℂ a := by
    simpa [a, Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 1) 0).symm
  have hm20 : M 2 0 = starRingEnd ℂ c := by
    simpa [c, Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 0).symm
  have hm21 : M 2 1 = starRingEnd ℂ b := by
    simpa [b, Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 1).symm
  have hsq : ‖c - a * b‖ ^ 2 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    by_cases ha : ‖a‖ ^ 2 < 1
    · let v : Fin 3 → ℂ := ![a * b - c, -(b - starRingEnd ℂ a * c), ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)]
      have hquad := (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg v)).1
      rw [Complex.zero_re] at hquad
      have hmul0 : (M.mulVec v) 0 = 0 := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, hm00]
        change 1 * (a * b - c) + a * -(b - starRingEnd ℂ a * c) + c * ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 0
        rw [Complex.ofReal_sub, Complex.ofReal_one]
        linear_combination c * (norm_sq_eq_mul_conj a).symm
      have hmul1 : (M.mulVec v) 1 = 0 := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, hm11, hm10]
        rw [Complex.ofReal_sub, Complex.ofReal_one]
        linear_combination b * (norm_sq_eq_mul_conj a).symm
      have hmul2 : ((M.mulVec v) 2).re =
          1 + 2 * (a * b * starRingEnd ℂ c).re - ‖a‖ ^ 2 - ‖b‖ ^ 2 - ‖c‖ ^ 2 := by
        have hm2C : (M.mulVec v) 2 =
            starRingEnd ℂ c * (a * b - c) + starRingEnd ℂ b * -(b - starRingEnd ℂ a * c) +
              ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val, hm22, hm20, hm21, one_mul]
        rw [hm2C]
        have hstep1 : starRingEnd ℂ c * (a * b - c) + starRingEnd ℂ b * -(b - starRingEnd ℂ a * c) +
            ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) =
            ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) - ((‖b‖ ^ 2 : ℝ) : ℂ) - ((‖c‖ ^ 2 : ℝ) : ℂ) +
              a * b * starRingEnd ℂ c + starRingEnd ℂ (a * b * starRingEnd ℂ c) := by
          rw [norm_sq_eq_mul_conj b, norm_sq_eq_mul_conj c]
          simp only [map_mul, Complex.conj_conj]
          ring
        rw [hstep1]
        simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, re_conj_eq_re]
        ring
      have hre_dot : (star v ⬝ᵥ M.mulVec v).re =
          (1 - ‖a‖ ^ 2) * (1 + 2 * (a * b * starRingEnd ℂ c).re - ‖a‖ ^ 2 - ‖b‖ ^ 2 - ‖c‖ ^ 2) := by
        rw [dotProduct, Fin.sum_univ_three, hmul0, hmul1]
        simp only [Pi.star_apply, Complex.star_def, mul_zero, zero_add]
        change (starRingEnd ℂ ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * (M.mulVec v) 2).re = _
        rw [Complex.conj_ofReal, Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rw [hmul2]
      rw [hre_dot] at hquad
      have hpos : 0 < 1 - ‖a‖ ^ 2 := sub_pos.mpr ha
      have hdet : 0 ≤ 1 + 2 * (a * b * starRingEnd ℂ c).re - ‖a‖ ^ 2 - ‖b‖ ^ 2 - ‖c‖ ^ 2 := by
        nlinarith
      exact (Matematyka.Malkoun.malkoun_lemma_5_1_core a b c).mp hdet
    · have ha_sq : ‖a‖ ^ 2 = 1 := le_antisymm (by nlinarith [norm_nonneg a]) (not_lt.mp ha)
      let q := b - starRingEnd ℂ a * c
      have hq : q = 0 := by
        by_contra hq_nz
        have hq2 : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq_nz)
        let r : ℝ := -1 / ‖q‖ ^ 2
        let s : ℂ := (r : ℂ) * q
        let v : Fin 3 → ℂ := ![-s * a, s, 1]
        have hquad := (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg v)).1
        rw [Complex.zero_re] at hquad
        have hmul0 : (M.mulVec v) 0 = c := by
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val, hm00]
          change 1 * (-s * a) + a * s + c * 1 = c; ring
        have hmul1 : (M.mulVec v) 1 = b := by
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val, hm11, hm10]
          change starRingEnd ℂ a * (-s * a) + 1 * s + b * 1 = b
          have haC : a * starRingEnd ℂ a = (1 : ℂ) := by
            rw [← norm_sq_eq_mul_conj a, ha_sq, Complex.ofReal_one]
          linear_combination -s * haC
        have hmul2 : (M.mulVec v) 2 = s * starRingEnd ℂ q + 1 := by
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val, hm22, hm20, hm21]
          change starRingEnd ℂ c * (-s * a) + starRingEnd ℂ b * s + 1 * 1 = s * starRingEnd ℂ q + 1
          simp only [q, map_sub, map_mul, Complex.conj_conj]; ring
        have hdot : star v ⬝ᵥ M.mulVec v =
            starRingEnd ℂ s * q + s * starRingEnd ℂ q + 1 := by
          rw [dotProduct, Fin.sum_univ_three, hmul0, hmul1, hmul2]
          simp only [Pi.star_apply, Complex.star_def, v, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val, map_one, one_mul, map_mul, map_neg, q]
          ring
        have hsq_q : starRingEnd ℂ s * q = (-1 : ℂ) := by
          have hr_nz : ‖q‖ ^ 2 ≠ 0 := hq2.ne'
          simp only [s, map_mul, Complex.conj_ofReal]
          calc ((r : ℂ) * starRingEnd ℂ q) * q
              = (r : ℂ) * (q * starRingEnd ℂ q) := by ring
            _ = (r : ℂ) * ((‖q‖ ^ 2 : ℝ) : ℂ) := by rw [← norm_sq_eq_mul_conj q]
            _ = ((r * ‖q‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
            _ = ((-1 : ℝ) : ℂ) := by congr 1; dsimp [r]; field_simp [hr_nz]
            _ = (-1 : ℂ) := by simp
        have hs_q : s * starRingEnd ℂ q = (-1 : ℂ) := by
          simpa [map_mul, Complex.conj_conj] using congrArg (starRingEnd ℂ) hsq_q
        rw [hdot, hsq_q, hs_q] at hquad
        norm_num at hquad
      have hb_eq : b = starRingEnd ℂ a * c := sub_eq_zero.mp hq
      have hcab : c - a * b = 0 := by
        rw [hb_eq]
        calc c - a * (starRingEnd ℂ a * c)
            = c - (a * starRingEnd ℂ a) * c := by ring
          _ = c - ((‖a‖ ^ 2 : ℝ) : ℂ) * c := by rw [norm_sq_eq_mul_conj a]
          _ = c - 1 * c := by rw [ha_sq, Complex.ofReal_one]
          _ = 0 := by ring
      have hb1 : ‖b‖ ≤ 1 := posSemidef_unitDiag_norm_le_one H hH hdiag j k
      have h1a : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
      have h1b : 0 ≤ 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
      rw [hcab, norm_zero, zero_pow two_ne_zero]
      exact mul_nonneg h1a h1b
  change ‖c - a * b‖ ≤ Real.sqrt ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2))
  exact Real.le_sqrt_of_sq_le hsq

/-- Matrix-level Conjecture C for $LG_3$ ($m = 2$). -/
theorem psd_path3_re_ge_one (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.PosSemidef) (hdiag : ∀ i, M i i = 1) :
    1 ≤ (M 0 0 * M 1 1 + M 0 1 * M 1 0).re := by
  have hm10 : M 1 0 = starRingEnd ℂ (M 0 1) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hM.isHermitian.eq 1) 0).symm
  rw [hdiag 0, hdiag 1, hm10, ← norm_sq_eq_mul_conj (M 0 1)]
  simp only [one_mul, Complex.add_re, Complex.one_re, Complex.ofReal_re]
  linarith [sq_nonneg ‖M 0 1‖]

/-- Matrix-level Conjecture C for $LG_4$ ($m = 3$). -/
theorem psd_path4_re_ge_one (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hM : M.PosSemidef) (hdiag : ∀ i, M i i = 1) :
    1 ≤ (M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 0 * M 2 2 +
      M 0 0 * M 2 1 * M 1 2 + M 0 1 * M 2 0 * M 1 2).re := by
  have hherm := hM.isHermitian
  have hm10 : M 1 0 = starRingEnd ℂ (M 0 1) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 1) 0).symm
  have hm20 : M 2 0 = starRingEnd ℂ (M 0 2) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 0).symm
  have hm21 : M 2 1 = starRingEnd ℂ (M 1 2) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 1).symm
  let a := M 0 1
  let b := M 1 2
  let c := M 0 2
  let δ := c - a * b
  have hc : c = a * b + δ := by dsimp [δ]; ring
  have ha1 : ‖a‖ ≤ 1 := posSemidef_unitDiag_norm_le_one M hM hdiag 0 1
  have hb1 : ‖b‖ ≤ 1 := posSemidef_unitDiag_norm_le_one M hM hdiag 1 2
  have hδ : ‖δ‖ ≤ Real.sqrt ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2)) :=
    posSemidef_unitDiag_three_disk_bound M hM hdiag 0 1 2
  have hsum : (M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 0 * M 2 2 +
      M 0 0 * M 2 1 * M 1 2 + M 0 1 * M 2 0 * M 1 2).re =
      1 + ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖a‖ ^ 2 * ‖b‖ ^ 2 + (a * b * starRingEnd ℂ δ).re := by
    rw [hdiag 0, hdiag 1, hdiag 2, hm10, hm20, hm21]
    dsimp only [a, b, c] at hc ⊢
    rw [hc, map_add]
    have haC : M 0 1 * starRingEnd ℂ (M 0 1) = ((‖a‖ ^ 2 : ℝ) : ℂ) := (norm_sq_eq_mul_conj (M 0 1)).symm
    have hbC : starRingEnd ℂ (M 1 2) * M 1 2 = ((‖b‖ ^ 2 : ℝ) : ℂ) := conj_mul_eq_norm_sq (M 1 2)
    have hmul : M 0 1 * (starRingEnd ℂ (M 0 1 * M 1 2) + starRingEnd ℂ δ) * M 1 2 =
        ((‖a‖ ^ 2 * ‖b‖ ^ 2 : ℝ) : ℂ) + a * b * starRingEnd ℂ δ := by
      rw [map_mul]
      calc M 0 1 * (starRingEnd ℂ (M 0 1) * starRingEnd ℂ (M 1 2) + starRingEnd ℂ δ) * M 1 2
          = (M 0 1 * starRingEnd ℂ (M 0 1)) * (starRingEnd ℂ (M 1 2) * M 1 2) +
              M 0 1 * M 1 2 * starRingEnd ℂ δ := by ring
        _ = ((‖a‖ ^ 2 : ℝ) : ℂ) * ((‖b‖ ^ 2 : ℝ) : ℂ) + a * b * starRingEnd ℂ δ := by
              rw [haC, hbC]
        _ = ((‖a‖ ^ 2 * ‖b‖ ^ 2 : ℝ) : ℂ) + a * b * starRingEnd ℂ δ := by push_cast; rfl
    have hsimp : 1 * 1 * 1 + M 0 1 * starRingEnd ℂ (M 0 1) * 1 + 1 * starRingEnd ℂ (M 1 2) * M 1 2 +
        M 0 1 * (starRingEnd ℂ (M 0 1 * M 1 2) + starRingEnd ℂ δ) * M 1 2 =
        1 + ((‖a‖ ^ 2 : ℝ) : ℂ) + ((‖b‖ ^ 2 : ℝ) : ℂ) +
        (((‖a‖ ^ 2 * ‖b‖ ^ 2 : ℝ) : ℂ) + a * b * starRingEnd ℂ δ) := by
      rw [← hmul, ← haC, ← hbC]; ring
    rw [hsimp]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    ring
  have hneg_re : -(a * b * starRingEnd ℂ δ).re ≤ ‖a‖ * ‖b‖ * ‖δ‖ := by
    have h := Complex.re_le_norm (-(a * b * starRingEnd ℂ δ))
    simpa only [Complex.neg_re, norm_neg, norm_mul, Complex.norm_conj] using h
  have hbound : 2 * (‖a‖ * ‖b‖ * ‖δ‖) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    have h1 : 2 * (‖a‖ * ‖b‖ * ‖δ‖) ≤
        2 * (‖a‖ * ‖b‖ * Real.sqrt ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2))) := by
      have hab : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith
    exact le_trans h1 (two_mul_sqrt_am_gm' ‖a‖ ‖b‖ (norm_nonneg _) ha1 (norm_nonneg _) hb1)
  rw [hsum]
  nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]

private def fin3PermFun : Fin 6 → Equiv.Perm (Fin 3)
  | 0 => 1
  | 1 => Equiv.swap 0 1
  | 2 => Equiv.swap 1 2
  | 3 => Equiv.swap 0 2
  | 4 => Equiv.swap 0 1 * Equiv.swap 1 2
  | 5 => Equiv.swap 1 2 * Equiv.swap 0 1

private def fin3PermEquiv : Fin 6 ≃ Equiv.Perm (Fin 3) where
  toFun := fin3PermFun
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

/-- Matrix-level Conjecture C for the claw graph $K_{1,3}$ ($3 \times 3$ permanent). -/
theorem psd_claw_re_ge_one (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hM : M.PosSemidef) (hdiag : ∀ i, M i i = 1) :
    1 ≤ (∑ σ : Equiv.Perm (Fin 3), ∏ i : Fin 3, M (σ i) i).re := by
  have hherm := hM.isHermitian
  have hm10 : M 1 0 = starRingEnd ℂ (M 0 1) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 1) 0).symm
  have hm20 : M 2 0 = starRingEnd ℂ (M 0 2) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 0).symm
  have hm21 : M 2 1 = starRingEnd ℂ (M 1 2) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 1).symm
  let a := M 0 1
  let b := M 1 2
  let c := M 0 2
  have hper : (∑ σ : Equiv.Perm (Fin 3), ∏ i : Fin 3, M (σ i) i) =
      M 0 0 * M 1 1 * M 2 2 +
      M 1 0 * M 0 1 * M 2 2 +
      M 0 0 * M 2 1 * M 1 2 +
      M 2 0 * M 1 1 * M 0 2 +
      M 1 0 * M 2 1 * M 0 2 +
      M 2 0 * M 0 1 * M 1 2 := by
    rw [← Fintype.sum_equiv fin3PermEquiv _ _ (fun _ => rfl), Fin.sum_univ_six]
    simp only [fin3PermEquiv, Equiv.coe_fn_mk, fin3PermFun, Fin.prod_univ_three,
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
  have hre : (∑ σ : Equiv.Perm (Fin 3), ∏ i : Fin 3, M (σ i) i).re =
      1 + ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + 2 * (a * b * starRingEnd ℂ c).re := by
    rw [hper, hdiag 0, hdiag 1, hdiag 2, hm10, hm20, hm21]
    have hsplit : (1 * 1 * 1 + starRingEnd ℂ a * a * 1 + 1 * starRingEnd ℂ b * b +
        starRingEnd ℂ c * 1 * c + starRingEnd ℂ a * starRingEnd ℂ b * c +
        starRingEnd ℂ c * a * b) =
        1 + ((‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 : ℝ) : ℂ) +
        (a * b * starRingEnd ℂ c + starRingEnd ℂ (a * b * starRingEnd ℂ c)) := by
      have ha : starRingEnd ℂ a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := conj_mul_eq_norm_sq a
      have hb : starRingEnd ℂ b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := conj_mul_eq_norm_sq b
      have hc : starRingEnd ℂ c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := conj_mul_eq_norm_sq c
      simp only [map_mul, Complex.conj_conj, Complex.ofReal_add]
      rw [← ha, ← hb, ← hc]; ring
    rw [hsplit]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, re_conj_eq_re]
    ring
  have hcomb : ‖c‖ ^ 2 + 2 * (a * b * starRingEnd ℂ c).re =
      ‖c + a * b‖ ^ 2 - ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_add_sq_identity c (a * b), norm_mul]
    ring
  have hb1 : ‖b‖ ≤ 1 := posSemidef_unitDiag_norm_le_one M hM hdiag 1 2
  have h1b : 0 ≤ 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  rw [hre]
  nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖, sq_nonneg ‖c + a * b‖, hcomb, h1b]

/-- Matrix-level Conjecture C for $LG_5$ ($m = 4$, Malkoun Theorem 4.4). -/
theorem psd_path5_re_ge_one (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : M.PosSemidef) (hdiag : ∀ i, M i i = 1) :
    1 ≤ (M 0 0 * M 1 1 * M 2 2 * M 3 3 +
      M 0 1 * M 1 0 * M 2 2 * M 3 3 +
      M 0 0 * M 1 1 * M 2 3 * M 3 2 +
      M 0 1 * M 1 0 * M 2 3 * M 3 2 +
      M 0 0 * M 2 1 * M 1 2 * M 3 3 +
      M 0 1 * M 2 0 * M 1 2 * M 3 3 +
      M 0 0 * M 2 1 * M 1 3 * M 3 2 +
      M 0 1 * M 2 0 * M 1 3 * M 3 2).re := by
  have hherm := hM.isHermitian
  have hm10 : M 1 0 = starRingEnd ℂ (M 0 1) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 1) 0).symm
  have hm20 : M 2 0 = starRingEnd ℂ (M 0 2) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 0).symm
  have hm21 : M 2 1 = starRingEnd ℂ (M 1 2) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 2) 1).symm
  have hm32 : M 3 2 = starRingEnd ℂ (M 2 3) := by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hherm.eq 3) 2).symm
  let a := M 0 1
  let b := M 1 2
  let c := M 2 3
  let m02 := M 0 2
  let m13 := M 1 3
  let δ1 := m02 - a * b
  let δ2 := m13 - b * c
  have hm02 : m02 = a * b + δ1 := by dsimp [δ1]; ring
  have hm13 : m13 = b * c + δ2 := by dsimp [δ2]; ring
  have ha1 : ‖a‖ ≤ 1 := posSemidef_unitDiag_norm_le_one M hM hdiag 0 1
  have hb1 : ‖b‖ ≤ 1 := posSemidef_unitDiag_norm_le_one M hM hdiag 1 2
  have hc1 : ‖c‖ ≤ 1 := posSemidef_unitDiag_norm_le_one M hM hdiag 2 3
  have hδ1 : ‖δ1‖ ≤ Real.sqrt ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2)) :=
    posSemidef_unitDiag_three_disk_bound M hM hdiag 0 1 2
  have hδ2 : ‖δ2‖ ≤ Real.sqrt ((1 - ‖b‖ ^ 2) * (1 - ‖c‖ ^ 2)) :=
    posSemidef_unitDiag_three_disk_bound M hM hdiag 1 2 3
  have halg :
      (M 0 0 * M 1 1 * M 2 2 * M 3 3 +
       M 0 1 * M 1 0 * M 2 2 * M 3 3 +
       M 0 0 * M 1 1 * M 2 3 * M 3 2 +
       M 0 1 * M 1 0 * M 2 3 * M 3 2 +
       M 0 0 * M 2 1 * M 1 2 * M 3 3 +
       M 0 1 * M 2 0 * M 1 2 * M 3 3 +
       M 0 0 * M 2 1 * M 1 3 * M 3 2 +
       M 0 1 * M 2 0 * M 1 3 * M 3 2) =
      (((1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2) * (1 + ‖c‖ ^ 2) : ℝ) : ℂ) +
      ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) * (a * b * starRingEnd ℂ δ1) +
      ((1 + ‖a‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ (b * c) * δ2) +
      (a * starRingEnd ℂ c) * (starRingEnd ℂ δ1 * δ2) := by
    rw [hdiag 0, hdiag 1, hdiag 2, hdiag 3, hm10, hm20, hm21, hm32]
    change (1 * 1 * 1 * 1 + a * starRingEnd ℂ a * 1 * 1 + 1 * 1 * c * starRingEnd ℂ c +
      a * starRingEnd ℂ a * c * starRingEnd ℂ c + 1 * starRingEnd ℂ b * b * 1 +
      a * starRingEnd ℂ m02 * b * 1 + 1 * starRingEnd ℂ b * m13 * starRingEnd ℂ c +
      a * starRingEnd ℂ m02 * m13 * starRingEnd ℂ c) = _
    rw [hm02, hm13]
    have haC : a * starRingEnd ℂ a = ((‖a‖ ^ 2 : ℝ) : ℂ) := (norm_sq_eq_mul_conj a).symm
    have hbC : b * starRingEnd ℂ b = ((‖b‖ ^ 2 : ℝ) : ℂ) := (norm_sq_eq_mul_conj b).symm
    have hcC : c * starRingEnd ℂ c = ((‖c‖ ^ 2 : ℝ) : ℂ) := (norm_sq_eq_mul_conj c).symm
    simp only [map_add, map_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one]
    rw [← haC, ← hbC, ← hcC]
    ring
  have hre_eq : (M 0 0 * M 1 1 * M 2 2 * M 3 3 +
      M 0 1 * M 1 0 * M 2 2 * M 3 3 +
      M 0 0 * M 1 1 * M 2 3 * M 3 2 +
      M 0 1 * M 1 0 * M 2 3 * M 3 2 +
      M 0 0 * M 2 1 * M 1 2 * M 3 3 +
      M 0 1 * M 2 0 * M 1 2 * M 3 3 +
      M 0 0 * M 2 1 * M 1 3 * M 3 2 +
      M 0 1 * M 2 0 * M 1 3 * M 3 2).re =
      (1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2) * (1 + ‖c‖ ^ 2) +
      (1 + ‖c‖ ^ 2) * (a * b * starRingEnd ℂ δ1).re +
      (1 + ‖a‖ ^ 2) * (starRingEnd ℂ (b * c) * δ2).re +
      ((a * starRingEnd ℂ c) * (starRingEnd ℂ δ1 * δ2)).re := by
    rw [halg]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  let s := Real.sqrt ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2))
  let t := Real.sqrt ((1 - ‖b‖ ^ 2) * (1 - ‖c‖ ^ 2))
  have hlem := Matematyka.Malkoun.malkoun_lemma_5_2 ‖a‖ ‖b‖ ‖c‖
    (norm_nonneg _) ha1 (norm_nonneg _) hb1 (norm_nonneg _) hc1
  dsimp only at hlem
  rcases hlem with ⟨hA, hB, hC⟩
  have hterm1 : -(a * b * starRingEnd ℂ δ1).re ≤ ‖a‖ * ‖b‖ * s := by
    have h := le_trans (Complex.re_le_norm (-(a * b * starRingEnd ℂ δ1))) (by
      simp only [norm_neg, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left hδ1 (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    simpa only [Complex.neg_re] using h
  have hterm2 : -(starRingEnd ℂ (b * c) * δ2).re ≤ ‖b‖ * ‖c‖ * t := by
    have h := le_trans (Complex.re_le_norm (-(starRingEnd ℂ (b * c) * δ2))) (by
      simp only [norm_neg, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left hδ2 (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    simpa only [Complex.neg_re] using h
  have hterm3 : -((a * starRingEnd ℂ c) * (starRingEnd ℂ δ1 * δ2)).re ≤ ‖a‖ * ‖c‖ * s * t := by
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hnorm : ‖-((a * starRingEnd ℂ c) * (starRingEnd ℂ δ1 * δ2))‖ =
        (‖a‖ * ‖c‖) * (‖δ1‖ * ‖δ2‖) := by
      simp only [norm_neg, norm_mul, Complex.norm_conj]
    have h12 : ‖δ1‖ * ‖δ2‖ ≤ s * t := mul_le_mul hδ1 hδ2 (norm_nonneg _) hs0
    have hprod : (‖a‖ * ‖c‖) * (‖δ1‖ * ‖δ2‖) ≤ (‖a‖ * ‖c‖) * (s * t) :=
      mul_le_mul_of_nonneg_left h12 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hre_neg : -((a * starRingEnd ℂ c) * (starRingEnd ℂ δ1 * δ2)).re ≤ (‖a‖ * ‖c‖) * (s * t) := by
      rw [← Complex.neg_re]
      exact (Complex.re_le_norm _).trans (by rw [hnorm]; exact hprod)
    exact hre_neg.trans_eq (mul_assoc (‖a‖ * ‖c‖) s t).symm
  have hc_pos : 0 ≤ 1 + ‖c‖ ^ 2 := by positivity
  have ha_pos : 0 ≤ 1 + ‖a‖ ^ 2 := by positivity
  have hbndA : -(1 + ‖c‖ ^ 2) * (a * b * starRingEnd ℂ δ1).re ≤ ‖a‖ * ‖b‖ * s * (1 + ‖c‖ ^ 2) := by
    nlinarith
  have hbndB : -(1 + ‖a‖ ^ 2) * (starRingEnd ℂ (b * c) * δ2).re ≤ ‖b‖ * ‖c‖ * t * (1 + ‖a‖ ^ 2) := by
    nlinarith
  rw [hre_eq]
  nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖, sq_nonneg ‖c‖,
    mul_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖b‖),
    mul_nonneg (sq_nonneg ‖b‖) (sq_nonneg ‖c‖),
    mul_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖c‖),
    mul_nonneg (mul_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖b‖)) (sq_nonneg ‖c‖)]

/-! ### Concrete 3D Graph Amplitude Theorems ($LG_3, LG_4, K_{1,3}, LG_5$) -/

/-- Path graph $LG_3$ on `Fin 3` (`0 - 1 - 2`). -/
def pathGraph3 : SimpleGraph (Fin 3) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance instDecidableRelPath3 : DecidableRel pathGraph3.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)))

/-- Path graph $LG_4$ on `Fin 4` (`0 - 1 - 2 - 3`). -/
def pathGraph4 : SimpleGraph (Fin 4) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance instDecidableRelPath4 : DecidableRel pathGraph4.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)))

/-- Claw graph $K_{1,3}$ on `Fin 4` with center `0` and leaves `1, 2, 3`. -/
def clawGraph : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1⟩

instance instDecidableRelClaw : DecidableRel clawGraph.Adj := fun u v =>
  inferInstanceAs (Decidable ((u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)))

/-- Path graph $LG_5$ on `Fin 5` (`0 - 1 - 2 - 3 - 4`). -/
def pathGraph5 : SimpleGraph (Fin 5) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance instDecidableRelPath5 : DecidableRel pathGraph5.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)))

private def partParity {n : ℕ} (u : Fin n) : Bool := decide (u.val % 2 = 1)

private lemma path_isBipartite_parity {n : ℕ} (G : SimpleGraph (Fin n))
    (hadj : ∀ u v : Fin n, G.Adj u v → (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)) :
    IsBipartite G partParity := by
  intro u v huv
  rcases hadj u v huv with h | h <;> simp [partParity] <;> omega

private def path3Edges : Fin 2 → BipEdge pathGraph3 partParity
  | 0 => ⟨(0, 1), by decide⟩
  | 1 => ⟨(2, 1), by decide⟩

private lemma path3_bipEdge_cases (e : BipEdge pathGraph3 partParity) :
    e = path3Edges 0 ∨ e = path3Edges 1 := by
  rcases e with ⟨⟨u, v⟩, hadj, hu, hv⟩
  have h : (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 1) := by
    revert u v hadj hu hv; decide
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [left; right] <;> rfl

private def path3EdgeEquiv : Fin 2 ≃ BipEdge pathGraph3 partParity where
  toFun := path3Edges
  invFun e := if e.1.1 = 0 then 0 else 1
  left_inv i := by fin_cases i <;> rfl
  right_inv e := by
    rcases path3_bipEdge_cases e with rfl | rfl <;> rfl

private instance : Unique (bipP1 pathGraph3 partParity) where
  default := 1
  uniq σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    have h1 := σ.2 e
    rcases path3_bipEdge_cases e with rfl | rfl <;>
      rcases path3_bipEdge_cases (σ.1 _) with h | h
    · exact h
    · exfalso; rw [h] at h1; exact absurd h1 (by decide)
    · exfalso; rw [h] at h1; exact absurd h1 (by decide)
    · exact h

private def path3Swap2 : Equiv.Perm (BipEdge pathGraph3 partParity) :=
  Equiv.swap (path3Edges 0) (path3Edges 1)

private def path3P2Equiv : Bool ≃ bipP2 pathGraph3 partParity where
  toFun b := if b then ⟨path3Swap2, fun e => by
    rcases path3_bipEdge_cases e with rfl | rfl <;> simp [path3Swap2, path3Edges]⟩ else 1
  invFun σ := decide (σ.1 (path3Edges 0) ≠ path3Edges 0)
  left_inv b := by cases b <;> simp [path3Swap2, path3Edges]
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro e
    have he0 := path3_bipEdge_cases (σ.1 (path3Edges 0))
    have he1 := path3_bipEdge_cases (σ.1 (path3Edges 1))
    have hne : σ.1 (path3Edges 0) ≠ σ.1 (path3Edges 1) :=
      fun h => (by decide : path3Edges 0 ≠ path3Edges 1) (σ.1.injective h)
    have he := path3_bipEdge_cases e
    dsimp only
    by_cases hfix : σ.1 (path3Edges 0) = path3Edges 0
    · rw [decide_eq_false (not_not.mpr hfix)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change e = σ.1 e
      rcases he1 with h10 | h11
      · exact absurd (hfix.trans h10.symm) hne
      · rcases he with rfl | rfl
        · exact hfix.symm
        · exact h11.symm
    · rw [decide_eq_true hfix]
      simp only [↓reduceIte]
      change path3Swap2 e = σ.1 e
      rcases he0 with h00 | h01
      · exact absurd h00 hfix
      · rcases he1 with h10 | h11
        · rcases he with rfl | rfl
          · rw [h01]; exact Equiv.swap_apply_left _ _
          · rw [h10]; exact Equiv.swap_apply_right _ _
        · exact absurd (h01.trans h11.symm) hne

/-- **Unconditional Conjecture C for $LG_3$ (`pathGraph3`):**
For every configuration $\mathbf{x} \in C_{LG_3}(\mathbb{R}^3)$,
$\operatorname{Re}(\mathcal{A}_{LG_3}(\mathbf{x})) \ge 1$, $\|\mathcal{A}_{LG_3}(\mathbf{x})\| \ge 1$, and $\mathcal{A}_{LG_3}(\mathbf{x}) \neq 0$. -/
theorem malkounAmplitude_path3_re_ge_one (x : ConfigSpace pathGraph3) :
    1 ≤ (malkounAmplitude pathGraph3 x).re := by
  have hb : IsBipartite pathGraph3 partParity := path_isBipartite_parity pathGraph3 fun _ _ h => h
  rw [malkounAmplitude_bipartite_eq_conj_gram pathGraph3 partParity hb x, Complex.conj_re]
  let M : Matrix (Fin 2) (Fin 2) ℂ := (bipGramMatrix pathGraph3 partParity x).submatrix path3Edges path3Edges
  have hM : M.PosSemidef := (bipGramMatrix_posSemidef pathGraph3 partParity x).submatrix path3Edges
  have hdiag : ∀ i : Fin 2, M i i = 1 := fun i => bipGramMatrix_diag_eq_one pathGraph3 partParity x _
  have hsum : (∑ σ₁ : bipP1 pathGraph3 partParity, ∑ σ₂ : bipP2 pathGraph3 partParity,
      ∏ e : BipEdge pathGraph3 partParity, bipGramMatrix pathGraph3 partParity x (σ₁.1 e) (σ₂.1 e)) =
      M 0 0 * M 1 1 + M 0 1 * M 1 0 := by
    rw [Fintype.sum_unique]
    change (∑ σ₂ : bipP2 pathGraph3 partParity, ∏ e, bipGramMatrix pathGraph3 partParity x e (σ₂.1 e)) = _
    rw [← Fintype.sum_equiv path3P2Equiv _ _ (fun _ => rfl), sum_bool_false_true]
    congr 1
    · rw [← Fintype.prod_equiv path3EdgeEquiv _ _ (fun _ => rfl), Fin.prod_univ_two]
      simp [path3P2Equiv, path3EdgeEquiv, M]
    · rw [← Fintype.prod_equiv path3EdgeEquiv _ _ (fun _ => rfl), Fin.prod_univ_two]
      simp [path3P2Equiv, path3Swap2, path3EdgeEquiv, M]
  rw [hsum]
  exact psd_path3_re_ge_one M hM hdiag

theorem malkounAmplitude_path3_abs_ge_one_and_ne_zero (x : ConfigSpace pathGraph3) :
    1 ≤ ‖malkounAmplitude pathGraph3 x‖ ∧ malkounAmplitude pathGraph3 x ≠ 0 := by
  have hre := malkounAmplitude_path3_re_ge_one x
  have hnorm : 1 ≤ ‖malkounAmplitude pathGraph3 x‖ := le_trans hre (Complex.re_le_norm _)
  refine ⟨hnorm, fun h0 => ?_⟩
  rw [h0, norm_zero] at hnorm
  linarith

private def path4Edges : Fin 3 → BipEdge pathGraph4 partParity
  | 0 => ⟨(0, 1), by decide⟩
  | 1 => ⟨(2, 1), by decide⟩
  | 2 => ⟨(2, 3), by decide⟩

private lemma path4_bipEdge_cases (e : BipEdge pathGraph4 partParity) :
    e = path4Edges 0 ∨ e = path4Edges 1 ∨ e = path4Edges 2 := by
  rcases e with ⟨⟨u, v⟩, hadj, hu, hv⟩
  have h : (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 1) ∨ (u = 2 ∧ v = 3) := by
    revert u v hadj hu hv; decide
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; rfl
  · right; left; rfl
  · right; right; rfl

private def path4EdgeEquiv : Fin 3 ≃ BipEdge pathGraph4 partParity where
  toFun := path4Edges
  invFun e := if e.1.1 = 0 then 0 else if e.1.2 = 1 then 1 else 2
  left_inv i := by fin_cases i <;> rfl
  right_inv e := by
    rcases path4_bipEdge_cases e with rfl | rfl | rfl <;> rfl

private def path4P1Equiv : Bool ≃ bipP1 pathGraph4 partParity where
  toFun b := if b then ⟨Equiv.swap (path4Edges 1) (path4Edges 2), fun e => by
    rcases path4_bipEdge_cases e with rfl | rfl | rfl <;> simp [path4Edges, Equiv.swap_apply_def]⟩ else 1
  invFun σ := decide (σ.1 (path4Edges 1) ≠ path4Edges 1)
  left_inv b := by cases b <;> simp [path4Edges]
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    have h0 := σ.2 (path4Edges 0)
    have h1 := σ.2 (path4Edges 1)
    have h2 := σ.2 (path4Edges 2)
    have he0 : σ.1 (path4Edges 0) = path4Edges 0 := by
      rcases path4_bipEdge_cases (σ.1 (path4Edges 0)) with h | h | h
      · exact h
      · exfalso; rw [h] at h0; revert h0; decide
      · exfalso; rw [h] at h0; revert h0; decide
    have he1 : σ.1 (path4Edges 1) = path4Edges 1 ∨ σ.1 (path4Edges 1) = path4Edges 2 := by
      rcases path4_bipEdge_cases (σ.1 (path4Edges 1)) with h | h | h
      · exfalso; rw [h] at h1; revert h1; decide
      · left; exact h
      · right; exact h
    have he2 : σ.1 (path4Edges 2) = path4Edges 1 ∨ σ.1 (path4Edges 2) = path4Edges 2 := by
      rcases path4_bipEdge_cases (σ.1 (path4Edges 2)) with h | h | h
      · exfalso; rw [h] at h2; revert h2; decide
      · left; exact h
      · right; exact h
    have hne : σ.1 (path4Edges 1) ≠ σ.1 (path4Edges 2) :=
      fun h => (by decide : path4Edges 1 ≠ path4Edges 2) (σ.1.injective h)
    have he := path4_bipEdge_cases e
    dsimp only
    by_cases hfix : σ.1 (path4Edges 1) = path4Edges 1
    · rw [decide_eq_false (not_not.mpr hfix)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change e = σ.1 e
      rcases he2 with h21 | h22
      · exact absurd (hfix.trans h21.symm) hne
      · rcases he with rfl | rfl | rfl
        · exact he0.symm
        · exact hfix.symm
        · exact h22.symm
    · rw [decide_eq_true hfix]
      simp only [↓reduceIte]
      change Equiv.swap (path4Edges 1) (path4Edges 2) e = σ.1 e
      rcases he1 with h11 | h12
      · exact absurd h11 hfix
      · rcases he2 with h21 | h22
        · rcases he with rfl | rfl | rfl
          · rw [he0]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
          · rw [h12]; exact Equiv.swap_apply_left _ _
          · rw [h21]; exact Equiv.swap_apply_right _ _
        · exact absurd (h12.trans h22.symm) hne

private def path4P2Equiv : Bool ≃ bipP2 pathGraph4 partParity where
  toFun b := if b then ⟨Equiv.swap (path4Edges 0) (path4Edges 1), fun e => by
    rcases path4_bipEdge_cases e with rfl | rfl | rfl <;> simp [path4Edges, Equiv.swap_apply_def]⟩ else 1
  invFun σ := decide (σ.1 (path4Edges 0) ≠ path4Edges 0)
  left_inv b := by cases b <;> simp [path4Edges]
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    have h0 := σ.2 (path4Edges 0)
    have h1 := σ.2 (path4Edges 1)
    have h2 := σ.2 (path4Edges 2)
    have he2 : σ.1 (path4Edges 2) = path4Edges 2 := by
      rcases path4_bipEdge_cases (σ.1 (path4Edges 2)) with h | h | h
      · exfalso; rw [h] at h2; revert h2; decide
      · exfalso; rw [h] at h2; revert h2; decide
      · exact h
    have he0 : σ.1 (path4Edges 0) = path4Edges 0 ∨ σ.1 (path4Edges 0) = path4Edges 1 := by
      rcases path4_bipEdge_cases (σ.1 (path4Edges 0)) with h | h | h
      · left; exact h
      · right; exact h
      · exfalso; rw [h] at h0; revert h0; decide
    have he1 : σ.1 (path4Edges 1) = path4Edges 0 ∨ σ.1 (path4Edges 1) = path4Edges 1 := by
      rcases path4_bipEdge_cases (σ.1 (path4Edges 1)) with h | h | h
      · left; exact h
      · right; exact h
      · exfalso; rw [h] at h1; revert h1; decide
    have hne : σ.1 (path4Edges 0) ≠ σ.1 (path4Edges 1) :=
      fun h => (by decide : path4Edges 0 ≠ path4Edges 1) (σ.1.injective h)
    have he := path4_bipEdge_cases e
    dsimp only
    by_cases hfix : σ.1 (path4Edges 0) = path4Edges 0
    · rw [decide_eq_false (not_not.mpr hfix)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change e = σ.1 e
      rcases he1 with h10 | h11
      · exact absurd (hfix.trans h10.symm) hne
      · rcases he with rfl | rfl | rfl
        · exact hfix.symm
        · exact h11.symm
        · exact he2.symm
    · rw [decide_eq_true hfix]
      simp only [↓reduceIte]
      change Equiv.swap (path4Edges 0) (path4Edges 1) e = σ.1 e
      rcases he0 with h00 | h01
      · exact absurd h00 hfix
      · rcases he1 with h10 | h11
        · rcases he with rfl | rfl | rfl
          · rw [h01]; exact Equiv.swap_apply_left _ _
          · rw [h10]; exact Equiv.swap_apply_right _ _
          · rw [he2]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
        · exact absurd (h01.trans h11.symm) hne

/-- **Unconditional Conjecture C for $LG_4$ (`pathGraph4`):**
For every configuration $\mathbf{x} \in C_{LG_4}(\mathbb{R}^3)$,
$\operatorname{Re}(\mathcal{A}_{LG_4}(\mathbf{x})) \ge 1$, $\|\mathcal{A}_{LG_4}(\mathbf{x})\| \ge 1$, and $\mathcal{A}_{LG_4}(\mathbf{x}) \neq 0$. -/
theorem malkounAmplitude_path4_re_ge_one (x : ConfigSpace pathGraph4) :
    1 ≤ (malkounAmplitude pathGraph4 x).re := by
  have hb : IsBipartite pathGraph4 partParity := path_isBipartite_parity pathGraph4 fun _ _ h => h
  rw [malkounAmplitude_bipartite_eq_conj_gram pathGraph4 partParity hb x, Complex.conj_re]
  let M : Matrix (Fin 3) (Fin 3) ℂ := (bipGramMatrix pathGraph4 partParity x).submatrix path4Edges path4Edges
  have hM : M.PosSemidef := (bipGramMatrix_posSemidef pathGraph4 partParity x).submatrix path4Edges
  have hdiag : ∀ i : Fin 3, M i i = 1 := fun i => bipGramMatrix_diag_eq_one pathGraph4 partParity x _
  have hsum : (∑ σ₁ : bipP1 pathGraph4 partParity, ∑ σ₂ : bipP2 pathGraph4 partParity,
      ∏ e : BipEdge pathGraph4 partParity, bipGramMatrix pathGraph4 partParity x (σ₁.1 e) (σ₂.1 e)) =
      M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 0 * M 2 2 +
      M 0 0 * M 2 1 * M 1 2 + M 0 1 * M 2 0 * M 1 2 := by
    rw [← Fintype.sum_equiv path4P1Equiv _ _ (fun _ => rfl), sum_bool_false_true]
    simp_rw [← Fintype.sum_equiv path4P2Equiv _ _ (fun _ => rfl), sum_bool_false_true]
    have hprod : ∀ (σ₁ : bipP1 pathGraph4 partParity) (σ₂ : bipP2 pathGraph4 partParity),
        (∏ e : BipEdge pathGraph4 partParity, bipGramMatrix pathGraph4 partParity x (σ₁.1 e) (σ₂.1 e)) =
        ∏ i : Fin 3, bipGramMatrix pathGraph4 partParity x (σ₁.1 (path4Edges i)) (σ₂.1 (path4Edges i)) :=
      fun σ₁ σ₂ => (Fintype.prod_equiv path4EdgeEquiv _ _ (fun _ => rfl)).symm
    simp_rw [hprod, Fin.prod_univ_three]
    have hm1_f : ∀ i : Fin 3, (path4P1Equiv false).1 (path4Edges i) = path4Edges i := fun _ => rfl
    have hm1_t : ∀ i : Fin 3, (path4P1Equiv true).1 (path4Edges i) =
        path4Edges (![0, 2, 1] i) := fun i => by fin_cases i <;> decide
    have hm2_f : ∀ i : Fin 3, (path4P2Equiv false).1 (path4Edges i) = path4Edges i := fun _ => rfl
    have hm2_t : ∀ i : Fin 3, (path4P2Equiv true).1 (path4Edges i) =
        path4Edges (![1, 0, 2] i) := fun i => by fin_cases i <;> decide
    simp only [hm1_f, hm1_t, hm2_f, hm2_t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    change (M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 0 * M 2 2) +
      (M 0 0 * M 2 1 * M 1 2 + M 0 1 * M 2 0 * M 1 2) = _
    ring
  rw [hsum]
  exact psd_path4_re_ge_one M hM hdiag

theorem malkounAmplitude_path4_abs_ge_one_and_ne_zero (x : ConfigSpace pathGraph4) :
    1 ≤ ‖malkounAmplitude pathGraph4 x‖ ∧ malkounAmplitude pathGraph4 x ≠ 0 := by
  have hre := malkounAmplitude_path4_re_ge_one x
  have hnorm : 1 ≤ ‖malkounAmplitude pathGraph4 x‖ := le_trans hre (Complex.re_le_norm _)
  refine ⟨hnorm, fun h0 => ?_⟩
  rw [h0, norm_zero] at hnorm
  linarith

private def clawPart : Fin 4 → Bool
  | 0 => false
  | _ => true

private def clawEdges : Fin 3 → BipEdge clawGraph clawPart
  | 0 => ⟨(0, 1), by decide⟩
  | 1 => ⟨(0, 2), by decide⟩
  | 2 => ⟨(0, 3), by decide⟩

private lemma claw_bipEdge_cases (e : BipEdge clawGraph clawPart) :
    e = clawEdges 0 ∨ e = clawEdges 1 ∨ e = clawEdges 2 := by
  rcases e with ⟨⟨u, v⟩, hadj, hu, hv⟩
  have h : (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 3) := by
    revert u v hadj hu hv; decide
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; rfl
  · right; left; rfl
  · right; right; rfl

private def clawEdgeEquiv : Fin 3 ≃ BipEdge clawGraph clawPart where
  toFun := clawEdges
  invFun e := if e.1.2 = 1 then 0 else if e.1.2 = 2 then 1 else 2
  left_inv i := by fin_cases i <;> rfl
  right_inv e := by
    rcases claw_bipEdge_cases e with rfl | rfl | rfl <;> rfl

private instance : Unique (bipP2 clawGraph clawPart) where
  default := 1
  uniq σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    have h2 := σ.2 e
    rcases claw_bipEdge_cases e with rfl | rfl | rfl <;>
      rcases claw_bipEdge_cases (σ.1 _) with h | h | h <;>
      first | exact h | (exfalso; rw [h] at h2; exact absurd h2 (by decide))

private def clawP1Equiv : Equiv.Perm (Fin 3) ≃ bipP1 clawGraph clawPart where
  toFun τ := ⟨Equiv.permCongr clawEdgeEquiv τ, fun e => by
    have h0 : ∀ x : BipEdge clawGraph clawPart, x.1.1 = 0 := fun x => by
      rcases claw_bipEdge_cases x with rfl | rfl | rfl <;> rfl
    exact (h0 _).trans (h0 e).symm⟩
  invFun σ := Equiv.permCongr clawEdgeEquiv.symm σ.1
  left_inv τ := by
    ext i
    simp [Equiv.permCongr_apply]
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro e
    simp [Equiv.permCongr_apply]

/-- **Unconditional Conjecture C for the claw graph $K_{1,3}$ (`clawGraph`):**
For every configuration $\mathbf{x} \in C_{K_{1,3}}(\mathbb{R}^3)$,
$\operatorname{Re}(\mathcal{A}_{K_{1,3}}(\mathbf{x})) \ge 1$, $\|\mathcal{A}_{K_{1,3}}(\mathbf{x})\| \ge 1$, and $\mathcal{A}_{K_{1,3}}(\mathbf{x}) \neq 0$. -/
theorem malkounAmplitude_claw_re_ge_one (x : ConfigSpace clawGraph) :
    1 ≤ (malkounAmplitude clawGraph x).re := by
  have hb : IsBipartite clawGraph clawPart := fun u v huv => by
    revert u v huv; decide
  rw [malkounAmplitude_bipartite_eq_conj_gram clawGraph clawPart hb x, Complex.conj_re]
  let M : Matrix (Fin 3) (Fin 3) ℂ := (bipGramMatrix clawGraph clawPart x).submatrix clawEdges clawEdges
  have hM : M.PosSemidef := (bipGramMatrix_posSemidef clawGraph clawPart x).submatrix clawEdges
  have hdiag : ∀ i : Fin 3, M i i = 1 := fun i => bipGramMatrix_diag_eq_one clawGraph clawPart x _
  have hsum : (∑ σ₁ : bipP1 clawGraph clawPart, ∑ σ₂ : bipP2 clawGraph clawPart,
      ∏ e : BipEdge clawGraph clawPart, bipGramMatrix clawGraph clawPart x (σ₁.1 e) (σ₂.1 e)) =
      ∑ τ : Equiv.Perm (Fin 3), ∏ i : Fin 3, M (τ i) i := by
    simp_rw [Fintype.sum_unique]
    rw [← Fintype.sum_equiv clawP1Equiv _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Fintype.prod_equiv clawEdgeEquiv _ _ (fun _ => rfl)]
    refine Finset.prod_congr rfl fun i _ => ?_
    change bipGramMatrix clawGraph clawPart x ((Equiv.permCongr clawEdgeEquiv τ) (clawEdges i))
        ((1 : bipP2 clawGraph clawPart).1 (clawEdges i)) = M (τ i) i
    fin_cases i <;> simp [Equiv.permCongr_apply, clawEdgeEquiv, clawEdges, M]
  rw [hsum]
  exact psd_claw_re_ge_one M hM hdiag

theorem malkounAmplitude_claw_abs_ge_one_and_ne_zero (x : ConfigSpace clawGraph) :
    1 ≤ ‖malkounAmplitude clawGraph x‖ ∧ malkounAmplitude clawGraph x ≠ 0 := by
  have hre := malkounAmplitude_claw_re_ge_one x
  have hnorm : 1 ≤ ‖malkounAmplitude clawGraph x‖ := le_trans hre (Complex.re_le_norm _)
  refine ⟨hnorm, fun h0 => ?_⟩
  rw [h0, norm_zero] at hnorm
  linarith

private def path5Edges : Fin 4 → BipEdge pathGraph5 partParity
  | 0 => ⟨(0, 1), by decide⟩
  | 1 => ⟨(2, 1), by decide⟩
  | 2 => ⟨(2, 3), by decide⟩
  | 3 => ⟨(4, 3), by decide⟩

private lemma path5_bipEdge_cases (e : BipEdge pathGraph5 partParity) :
    e = path5Edges 0 ∨ e = path5Edges 1 ∨ e = path5Edges 2 ∨ e = path5Edges 3 := by
  rcases e with ⟨⟨u, v⟩, hadj, hu, hv⟩
  have h : (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 1) ∨ (u = 2 ∧ v = 3) ∨ (u = 4 ∧ v = 3) := by
    revert u v hadj hu hv; decide
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; rfl

private def path5EdgeEquiv : Fin 4 ≃ BipEdge pathGraph5 partParity where
  toFun := path5Edges
  invFun e :=
    if e.1.1 = 0 then 0 else if e.1.2 = 1 then 1 else if e.1.1 = 2 then 2 else 3
  left_inv i := by fin_cases i <;> rfl
  right_inv e := by
    rcases path5_bipEdge_cases e with rfl | rfl | rfl | rfl <;> rfl

private def path5P1Equiv : Bool ≃ bipP1 pathGraph5 partParity where
  toFun b := if b then ⟨Equiv.swap (path5Edges 1) (path5Edges 2), fun e => by
    rcases path5_bipEdge_cases e with rfl | rfl | rfl | rfl <;>
      simp [path5Edges, Equiv.swap_apply_def]⟩ else 1
  invFun σ := decide (σ.1 (path5Edges 1) ≠ path5Edges 1)
  left_inv b := by cases b <;> simp [path5Edges]
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    have h0 := σ.2 (path5Edges 0)
    have h1 := σ.2 (path5Edges 1)
    have h2 := σ.2 (path5Edges 2)
    have h3 := σ.2 (path5Edges 3)
    have he0 : σ.1 (path5Edges 0) = path5Edges 0 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 0)) with h | h | h | h
      · exact h
      · exfalso; rw [h] at h0; revert h0; decide
      · exfalso; rw [h] at h0; revert h0; decide
      · exfalso; rw [h] at h0; revert h0; decide
    have he3 : σ.1 (path5Edges 3) = path5Edges 3 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 3)) with h | h | h | h
      · exfalso; rw [h] at h3; revert h3; decide
      · exfalso; rw [h] at h3; revert h3; decide
      · exfalso; rw [h] at h3; revert h3; decide
      · exact h
    have he1 : σ.1 (path5Edges 1) = path5Edges 1 ∨ σ.1 (path5Edges 1) = path5Edges 2 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 1)) with h | h | h | h
      · exfalso; rw [h] at h1; revert h1; decide
      · left; exact h
      · right; exact h
      · exfalso; rw [h] at h1; revert h1; decide
    have he2 : σ.1 (path5Edges 2) = path5Edges 1 ∨ σ.1 (path5Edges 2) = path5Edges 2 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 2)) with h | h | h | h
      · exfalso; rw [h] at h2; revert h2; decide
      · left; exact h
      · right; exact h
      · exfalso; rw [h] at h2; revert h2; decide
    have hne : σ.1 (path5Edges 1) ≠ σ.1 (path5Edges 2) :=
      fun h => (by decide : path5Edges 1 ≠ path5Edges 2) (σ.1.injective h)
    have he := path5_bipEdge_cases e
    dsimp only
    by_cases hfix : σ.1 (path5Edges 1) = path5Edges 1
    · rw [decide_eq_false (not_not.mpr hfix)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change e = σ.1 e
      rcases he2 with h21 | h22
      · exact absurd (hfix.trans h21.symm) hne
      · rcases he with rfl | rfl | rfl | rfl
        · exact he0.symm
        · exact hfix.symm
        · exact h22.symm
        · exact he3.symm
    · rw [decide_eq_true hfix]
      simp only [↓reduceIte]
      change Equiv.swap (path5Edges 1) (path5Edges 2) e = σ.1 e
      rcases he1 with h11 | h12
      · exact absurd h11 hfix
      · rcases he2 with h21 | h22
        · rcases he with rfl | rfl | rfl | rfl
          · rw [he0]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
          · rw [h12]; exact Equiv.swap_apply_left _ _
          · rw [h21]; exact Equiv.swap_apply_right _ _
          · rw [he3]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
        · exact absurd (h12.trans h22.symm) hne

private def path5P2Fun (p : Bool × Bool) : Equiv.Perm (BipEdge pathGraph5 partParity) :=
  (if p.1 then Equiv.swap (path5Edges 0) (path5Edges 1) else 1) *
  (if p.2 then Equiv.swap (path5Edges 2) (path5Edges 3) else 1)

private lemma path5P2Fun_apply (p1 p2 : Bool) (i : Fin 4) :
    path5P2Fun (p1, p2) (path5Edges i) =
      path5Edges ((if p1 then (if p2 then ![1, 0, 3, 2] else ![1, 0, 2, 3])
        else (if p2 then ![0, 1, 3, 2] else ![0, 1, 2, 3])) i) := by
  rcases p1 with _ | _ <;> rcases p2 with _ | _ <;> fin_cases i <;> decide

private def path5P2Equiv : (Bool × Bool) ≃ bipP2 pathGraph5 partParity where
  toFun p := ⟨path5P2Fun p, fun e => by
    rcases p with ⟨_ | _, _ | _⟩ <;> rcases path5_bipEdge_cases e with rfl | rfl | rfl | rfl <;>
      simp [path5P2Fun, path5Edges, Equiv.swap_apply_def]⟩
  invFun σ := (decide (σ.1 (path5Edges 0) ≠ path5Edges 0), decide (σ.1 (path5Edges 2) ≠ path5Edges 2))
  left_inv p := by rcases p with ⟨_ | _, _ | _⟩ <;> decide
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    have h0 := σ.2 (path5Edges 0)
    have h1 := σ.2 (path5Edges 1)
    have h2 := σ.2 (path5Edges 2)
    have h3 := σ.2 (path5Edges 3)
    have he0 : σ.1 (path5Edges 0) = path5Edges 0 ∨ σ.1 (path5Edges 0) = path5Edges 1 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 0)) with h | h | h | h
      · left; exact h
      · right; exact h
      · exfalso; rw [h] at h0; revert h0; decide
      · exfalso; rw [h] at h0; revert h0; decide
    have he1 : σ.1 (path5Edges 1) = path5Edges 0 ∨ σ.1 (path5Edges 1) = path5Edges 1 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 1)) with h | h | h | h
      · left; exact h
      · right; exact h
      · exfalso; rw [h] at h1; revert h1; decide
      · exfalso; rw [h] at h1; revert h1; decide
    have he2 : σ.1 (path5Edges 2) = path5Edges 2 ∨ σ.1 (path5Edges 2) = path5Edges 3 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 2)) with h | h | h | h
      · exfalso; rw [h] at h2; revert h2; decide
      · exfalso; rw [h] at h2; revert h2; decide
      · left; exact h
      · right; exact h
    have he3 : σ.1 (path5Edges 3) = path5Edges 2 ∨ σ.1 (path5Edges 3) = path5Edges 3 := by
      rcases path5_bipEdge_cases (σ.1 (path5Edges 3)) with h | h | h | h
      · exfalso; rw [h] at h3; revert h3; decide
      · exfalso; rw [h] at h3; revert h3; decide
      · left; exact h
      · right; exact h
    have hne01 : σ.1 (path5Edges 0) ≠ σ.1 (path5Edges 1) :=
      fun h => (by decide : path5Edges 0 ≠ path5Edges 1) (σ.1.injective h)
    have hne23 : σ.1 (path5Edges 2) ≠ σ.1 (path5Edges 3) :=
      fun h => (by decide : path5Edges 2 ≠ path5Edges 3) (σ.1.injective h)
    have he := path5_bipEdge_cases e
    change path5P2Fun (decide (σ.1 (path5Edges 0) ≠ path5Edges 0),
        decide (σ.1 (path5Edges 2) ≠ path5Edges 2)) e = σ.1 e
    rcases he0 with h00 | h01 <;> rcases he1 with h10 | h11 <;>
      rcases he2 with h22 | h23 <;> rcases he3 with h32 | h33
    · exact absurd (h00.trans h10.symm) hne01
    · exact absurd (h00.trans h10.symm) hne01
    · exact absurd (h00.trans h10.symm) hne01
    · exact absurd (h00.trans h10.symm) hne01
    · exact absurd (h22.trans h32.symm) hne23
    · rw [decide_eq_false (not_not.mpr h00), decide_eq_false (not_not.mpr h22)]
      rcases he with rfl | rfl | rfl | rfl <;> rw [path5P2Fun_apply]
      · exact h00.symm
      · exact h11.symm
      · exact h22.symm
      · exact h33.symm
    · have hne2 : path5Edges 3 ≠ path5Edges 2 := by decide
      rw [decide_eq_false (not_not.mpr h00), h23, decide_eq_true hne2]
      rcases he with rfl | rfl | rfl | rfl <;> rw [path5P2Fun_apply]
      · exact h00.symm
      · exact h11.symm
      · exact h23.symm
      · exact h32.symm
    · exact absurd (h23.trans h33.symm) hne23
    · exact absurd (h22.trans h32.symm) hne23
    · have hne0 : path5Edges 1 ≠ path5Edges 0 := by decide
      rw [h01, decide_eq_true hne0, decide_eq_false (not_not.mpr h22)]
      rcases he with rfl | rfl | rfl | rfl <;> rw [path5P2Fun_apply]
      · exact h01.symm
      · exact h10.symm
      · exact h22.symm
      · exact h33.symm
    · have hne0 : path5Edges 1 ≠ path5Edges 0 := by decide
      have hne2 : path5Edges 3 ≠ path5Edges 2 := by decide
      rw [h01, decide_eq_true hne0, h23, decide_eq_true hne2]
      rcases he with rfl | rfl | rfl | rfl <;> rw [path5P2Fun_apply]
      · exact h01.symm
      · exact h10.symm
      · exact h23.symm
      · exact h32.symm
    · exact absurd (h23.trans h33.symm) hne23
    · exact absurd (h01.trans h11.symm) hne01
    · exact absurd (h01.trans h11.symm) hne01
    · exact absurd (h01.trans h11.symm) hne01
    · exact absurd (h01.trans h11.symm) hne01

/-- **Unconditional Conjecture C for $LG_5$ (`pathGraph5`, Malkoun Theorem 4.4):**
For every configuration $\mathbf{x} \in C_{LG_5}(\mathbb{R}^3)$,
$\operatorname{Re}(\mathcal{A}_{LG_5}(\mathbf{x})) \ge 1$, $\|\mathcal{A}_{LG_5}(\mathbf{x})\| \ge 1$, and $\mathcal{A}_{LG_5}(\mathbf{x}) \neq 0$. -/
theorem malkounAmplitude_path5_re_ge_one (x : ConfigSpace pathGraph5) :
    1 ≤ (malkounAmplitude pathGraph5 x).re := by
  have hb : IsBipartite pathGraph5 partParity := path_isBipartite_parity pathGraph5 fun _ _ h => h
  rw [malkounAmplitude_bipartite_eq_conj_gram pathGraph5 partParity hb x, Complex.conj_re]
  let M : Matrix (Fin 4) (Fin 4) ℂ := (bipGramMatrix pathGraph5 partParity x).submatrix path5Edges path5Edges
  have hM : M.PosSemidef := (bipGramMatrix_posSemidef pathGraph5 partParity x).submatrix path5Edges
  have hdiag : ∀ i : Fin 4, M i i = 1 := fun i => bipGramMatrix_diag_eq_one pathGraph5 partParity x _
  have hsum : (∑ σ₁ : bipP1 pathGraph5 partParity, ∑ σ₂ : bipP2 pathGraph5 partParity,
      ∏ e : BipEdge pathGraph5 partParity, bipGramMatrix pathGraph5 partParity x (σ₁.1 e) (σ₂.1 e)) =
      M 0 0 * M 1 1 * M 2 2 * M 3 3 +
      M 0 1 * M 1 0 * M 2 2 * M 3 3 +
      M 0 0 * M 1 1 * M 2 3 * M 3 2 +
      M 0 1 * M 1 0 * M 2 3 * M 3 2 +
      M 0 0 * M 2 1 * M 1 2 * M 3 3 +
      M 0 1 * M 2 0 * M 1 2 * M 3 3 +
      M 0 0 * M 2 1 * M 1 3 * M 3 2 +
      M 0 1 * M 2 0 * M 1 3 * M 3 2 := by
    rw [← Fintype.sum_equiv path5P1Equiv _ _ (fun _ => rfl), sum_bool_false_true]
    simp_rw [← Fintype.sum_equiv path5P2Equiv _ _ (fun _ => rfl), Fintype.sum_prod_type, sum_bool_false_true]
    have hprod : ∀ (σ₁ : bipP1 pathGraph5 partParity) (σ₂ : bipP2 pathGraph5 partParity),
        (∏ e : BipEdge pathGraph5 partParity, bipGramMatrix pathGraph5 partParity x (σ₁.1 e) (σ₂.1 e)) =
        ∏ i : Fin 4, bipGramMatrix pathGraph5 partParity x (σ₁.1 (path5Edges i)) (σ₂.1 (path5Edges i)) :=
      fun σ₁ σ₂ => (Fintype.prod_equiv path5EdgeEquiv _ _ (fun _ => rfl)).symm
    simp_rw [hprod, Fin.prod_univ_four]
    have hm1_f : ∀ i : Fin 4, (path5P1Equiv false).1 (path5Edges i) = path5Edges i := fun i => rfl
    have hm1_t : ∀ i : Fin 4, (path5P1Equiv true).1 (path5Edges i) =
        path5Edges (![0, 2, 1, 3] i) := fun i => by fin_cases i <;> decide
    have hm2_ff : ∀ i : Fin 4, (path5P2Equiv (false, false)).1 (path5Edges i) = path5Edges i :=
      fun i => rfl
    have hm2_ft : ∀ i : Fin 4, (path5P2Equiv (false, true)).1 (path5Edges i) =
        path5Edges (![0, 1, 3, 2] i) := fun i => by fin_cases i <;> decide
    have hm2_tf : ∀ i : Fin 4, (path5P2Equiv (true, false)).1 (path5Edges i) =
        path5Edges (![1, 0, 2, 3] i) := fun i => by fin_cases i <;> decide
    have hm2_tt : ∀ i : Fin 4, (path5P2Equiv (true, true)).1 (path5Edges i) =
        path5Edges (![1, 0, 3, 2] i) := fun i => by fin_cases i <;> decide
    simp only [hm1_f, hm1_t, hm2_ff, hm2_ft, hm2_tf, hm2_tt, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    change ((M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 2 3 * M 3 2) +
        (M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2)) +
      ((M 0 0 * M 2 1 * M 1 2 * M 3 3 + M 0 0 * M 2 1 * M 1 3 * M 3 2) +
        (M 0 1 * M 2 0 * M 1 2 * M 3 3 + M 0 1 * M 2 0 * M 1 3 * M 3 2)) = _
    ring
  rw [hsum]
  exact psd_path5_re_ge_one M hM hdiag

theorem malkounAmplitude_path5_abs_ge_one_and_ne_zero (x : ConfigSpace pathGraph5) :
    1 ≤ ‖malkounAmplitude pathGraph5 x‖ ∧ malkounAmplitude pathGraph5 x ≠ 0 := by
  have hre := malkounAmplitude_path5_re_ge_one x
  have hnorm : 1 ≤ ‖malkounAmplitude pathGraph5 x‖ := le_trans hre (Complex.re_le_norm _)
  refine ⟨hnorm, fun h0 => ?_⟩
  rw [h0, norm_zero] at hnorm
  linarith

/-! ### Surviving Frontier: Tree-Restricted Conjecture D $\implies$ Conjecture C for All Trees -/

/-- Every finite acyclic graph (and hence every tree) admits an explicit `Bool` bipartition witness. -/
lemma isAcyclic_exists_isBipartite {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic) :
    ∃ part : Fin n → Bool, IsBipartite G part := by
  let c : G.Coloring (Fin 2) := Classical.choice hG.isBipartite
  refine ⟨fun u => decide (c u = 1), fun u v hadj => ?_⟩
  have hne : c u ≠ c v := c.valid hadj
  rcases fin2_eq_cases (c u) with hu | hu <;> rcases fin2_eq_cases (c v) with hv | hv
  · exact absurd (hu.trans hv.symm) hne
  · simp [hu, hv]
  · simp [hu, hv]
  · exact absurd (hu.trans hv.symm) hne

/-- **Tree-Restricted Conjecture D:** Malkoun's Gram-matrix inequality restricted specifically
to bipartite incidence partitions `(bipP1 T part, bipP2 T part)` of finite trees `T.IsTree`.
Formally refuted in `Matematyka.MalkounConjectureC` (`disproof_malkoun_tree_conjecture_D`)
via contraposition from `cherryTree10` and `treeConjectureD_implies_conjecture_C`. -/
def MalkounTreeConjectureDProp : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (_ : DecidableRel T.Adj)
    (part : Fin n → Bool) (_ : T.IsTree) (_ : IsBipartite T part)
    (B : Matrix (Fin 2) (BipEdge T part) ℂ),
    let H := B.conjTranspose * B
    (∑ σ₁ : bipP1 T part, ∑ σ₂ : bipP2 T part,
      ∏ e : BipEdge T part, H (σ₁.1 e) (σ₂.1 e)).re ≥
      ∏ e : BipEdge T part, (H e e).re

/-- **Tree Reduction Theorem (refuted hypothesis):** Tree-restricted Conjecture D implies
Malkoun's Conjecture C ($\operatorname{Re}(\mathcal{A}_T(\mathbf{x})) \ge 1$,
$\|\mathcal{A}_T(\mathbf{x})\| \ge 1$, $\mathcal{A}_T(\mathbf{x}) \neq 0$) for **every**
finite tree `T`. Both Conjecture C and `MalkounTreeConjectureDProp` are formally disproved in
`Matematyka.MalkounConjectureC` (`disproof_malkoun_conjecture_C`,
`disproof_malkoun_tree_conjecture_D`) on the 10-vertex planar pinwheel tree `cherryTree10`. -/
theorem treeConjectureD_implies_conjecture_C (hTD : MalkounTreeConjectureDProp)
    {n : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj] (hT : T.IsTree) (x : ConfigSpace T) :
    1 ≤ (malkounAmplitude T x).re ∧ 1 ≤ ‖malkounAmplitude T x‖ ∧ malkounAmplitude T x ≠ 0 := by
  rcases isAcyclic_exists_isBipartite T hT.isAcyclic with ⟨part, hb⟩
  have hre : 1 ≤ (malkounAmplitude T x).re := by
    rw [malkounAmplitude_bipartite_eq_conj_gram T part hb x, Complex.conj_re]
    let B : Matrix (Fin 2) (BipEdge T part) ℂ := fun k e => bipEdgeSpinor x e k
    have hB : B.conjTranspose * B = bipGramMatrix T part x := by
      ext a b
      exact matrix_fin2_conjMul_apply B a b
    have hineq := hTD n T inferInstance part hT hb B
    dsimp only at hineq
    rw [hB] at hineq
    have hdiag : ∀ e : BipEdge T part, (bipGramMatrix T part x e e).re = 1 := fun e => by
      rw [bipGramMatrix_diag_eq_one, Complex.one_re]
    rw [Finset.prod_eq_one (fun e _ => hdiag e)] at hineq
    exact hineq
  have hnorm : 1 ≤ ‖malkounAmplitude T x‖ := le_trans hre (Complex.re_le_norm _)
  refine ⟨hre, hnorm, fun h0 => ?_⟩
  rw [h0, norm_zero] at hnorm
  linarith

end TreePositivity

end Matematyka.MalkounConjectureD
