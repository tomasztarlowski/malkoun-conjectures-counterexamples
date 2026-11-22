import Matematyka.MalkounConjectureC

/-!
# Unconditional Path Positivity for Malkoun's $G$-Amplitude ($LG_n$ for All $n \in \mathbb{N}$)

This module resolves the remaining open positivity questions for Malkoun's linear path family
$LG_n$ (`pathGraphN n`) for **all** $n \in \mathbb{N}$ unconditionally in Lean 4:

1. **Path Conjecture B & Conjecture A (`malkounAmplitude_pathGraphN_norm_ge_one`, `malkounAmplitude_pathGraphN_ne_zero`):**
   For every $n \in \mathbb{N}$ and every non-collision configuration `x : ConfigSpace (pathGraphN n)`,
   `1 ≤ ‖malkounAmplitude (pathGraphN n) x‖` and `malkounAmplitude (pathGraphN n) x ≠ 0`.
   Even though $\operatorname{Re}(\mathcal{A}_{LG_n})$ turns negative at $n = 15$ (`MalkounConjectureC.lean`),
   the $\mathrm{SU}(2)$ spinor transfer recurrence $(a_k, w_k) \in \mathbb{C} \times \mathbb{C}^2$ obeys
   the exact hyperbolic Lyapunov identity
   $$(\|a_{k+1}\|^2 - \|\beta_{k+1}\|^2) - (\|a_k\|^2 - \|\beta_k\|^2) = \|U\|^2(3\|d\|^2 + \|c\|^2) \ge 0,$$
   keeping $|a_k|^2 - |\beta_k|^2 \ge 1$ and hence $\|\mathcal{A}_{LG_n}(\mathbf{x})\| \ge 1$ for all $n$.
2. **Planar Path Conjecture C (`malkounAmplitude_pathGraphN_planar_re_ge_one`):**
   Whenever `x` is planar (`∀ u, x.1 u 2 = 0`), every normalized inner product along the Cayley-rotated
   spinor gauge is real, preserving `0 < a_k` and thus `1 ≤ (malkounAmplitude (pathGraphN n) x).re`
   for **all** $n \in \mathbb{N}$.
-/

namespace Matematyka.MalkounPathPositivity

open Complex Real Classical Matematyka.MalkounCounterexample Matematyka.MalkounBipartite
  Matematyka.MalkounConjectureD Matematyka.MalkounConjectureC

/-! ## Part 1: Arbitrary-Length Path Graph `pathGraphN`, Bipartite Structure, and Swap Subgroups -/

section PathGraphNDef

/-- Linear path graph $LG_n$ on `Fin n`. -/
def pathGraphN (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance instDecidableRelPathN (n : ℕ) : DecidableRel (pathGraphN n).Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)))

theorem pathGraphN_connected {n : ℕ} (hn : 1 ≤ n) : (pathGraphN n).Connected := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hr : ∀ (k : ℕ) (hk : k < n), (pathGraphN n).Reachable ⟨0, hn⟩ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ k ih =>
        intro hk
        have hadj : (pathGraphN n).Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ := Or.inl rfl
        exact (ih (by omega)).trans hadj.reachable
  exact ⟨fun u v => (hr u.val u.isLt).symm.trans (hr v.val v.isLt)⟩

private def pathEdgeSetEquiv (m : ℕ) : Fin m ≃ (pathGraphN (m + 1)).edgeSet where
  toFun i := ⟨s(⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩), Or.inl rfl⟩
  invFun e := ⟨Sym2.lift ⟨fun u v => min u.val v.val, fun u v => by simp [min_comm]⟩ e.1, by
    rcases e with ⟨s, hs⟩
    induction s using Sym2.ind with
    | _ u v =>
      have hadj : (pathGraphN (m + 1)).Adj u v := hs
      have hu := u.isLt
      have hv := v.isLt
      dsimp only [pathGraphN, Sym2.lift_mk] at hadj ⊢
      rcases hadj with h | h <;> cases min_cases u.val v.val <;> omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp only [Sym2.lift_mk]
    omega
  right_inv e := by
    apply Subtype.ext
    rcases e with ⟨s, hs⟩
    induction s using Sym2.ind with
    | _ u v =>
      have hadj : (pathGraphN (m + 1)).Adj u v := hs
      dsimp only [pathGraphN, Sym2.lift_mk] at hadj ⊢
      rcases hadj with h | h
      · have hu := u.isLt; have hv := v.isLt
        have heq1 : (⟨min u.val v.val, Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hu⟩ : Fin (m + 1)) = u :=
          Fin.ext (min_eq_left (by omega))
        have heq2 : (⟨min u.val v.val + 1, by simp only [min_def]; split_ifs <;> omega⟩ : Fin (m + 1)) = v :=
          Fin.ext (by simp only [min_def]; split_ifs <;> omega)
        rw [heq1, heq2]
      · have hu := u.isLt; have hv := v.isLt
        have heq1 : (⟨min u.val v.val, Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hv⟩ : Fin (m + 1)) = v :=
          Fin.ext (min_eq_right (by omega))
        have heq2 : (⟨min u.val v.val + 1, by simp only [min_def]; split_ifs <;> omega⟩ : Fin (m + 1)) = u :=
          Fin.ext (by simp only [min_def]; split_ifs <;> omega)
        rw [heq1, heq2, Sym2.eq_swap]

theorem pathGraphN_isTree {n : ℕ} (hn : 1 ≤ n) : (pathGraphN n).IsTree := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨pathGraphN_connected hn, ?_⟩
  have hcard : Nat.card (pathGraphN (m + 1)).edgeSet = m := by
    rw [Nat.card_congr (pathEdgeSetEquiv m).symm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Alternating vertex bipartition on `Fin n`: odd vertices `false`, even vertices `true`. -/
def partEvenN {n : ℕ} (u : Fin n) : Bool := decide (u.val % 2 = 0)

lemma pathGraphN_isBipartite (n : ℕ) : IsBipartite (pathGraphN n) partEvenN := by
  intro u v huv
  rcases huv with h | h <;> simp [partEvenN] <;> omega

private def pathNEdgeEnd (m : ℕ) (e : Fin m) : Fin (m + 1) × Fin (m + 1) :=
  if e.val % 2 = 0 then (⟨e.val + 1, by omega⟩, ⟨e.val, by omega⟩)
  else (⟨e.val, by omega⟩, ⟨e.val + 1, by omega⟩)

private def pathNEdges (m : ℕ) (e : Fin m) : BipEdge (pathGraphN (m + 1)) partEvenN :=
  ⟨pathNEdgeEnd m e, by
    unfold pathNEdgeEnd
    split_ifs with h
    · refine ⟨Or.inr rfl, ?_, ?_⟩ <;> simp [partEvenN] <;> omega
    · refine ⟨Or.inl rfl, ?_, ?_⟩ <;> simp [partEvenN] <;> omega⟩

private def pathNEdgeEquiv (m : ℕ) : Fin m ≃ BipEdge (pathGraphN (m + 1)) partEvenN where
  toFun := pathNEdges m
  invFun e := ⟨min e.1.1.val e.1.2.val, by
    rcases e with ⟨⟨u, v⟩, hadj, _⟩
    have hu := u.isLt
    have hv := v.isLt
    dsimp only at hadj ⊢
    rcases hadj with h | h <;> cases min_cases u.val v.val <;> omega⟩
  left_inv e := by
    apply Fin.ext
    dsimp only [pathNEdges, pathNEdgeEnd]
    split_ifs <;> dsimp only <;> cases min_cases (e.val + 1) e.val <;> omega
  right_inv e := by
    apply Subtype.ext
    rcases e with ⟨⟨⟨uv, huv⟩, ⟨vv, hvv⟩⟩, hadj, hu, hv⟩
    dsimp only [pathNEdges, pathNEdgeEnd]
    have hu_mod : uv % 2 = 1 := by simp [partEvenN] at hu; omega
    have hv_mod : vv % 2 = 0 := by simp [partEvenN] at hv; omega
    rcases hadj with h | h
    · have h1 : min uv vv = uv := min_eq_left (by dsimp only at h; omega)
      have hm : ¬ (min uv vv % 2 = 0) := by omega
      simp only [hm, ↓reduceIte]
      exact Prod.ext (Fin.ext (by dsimp only at h ⊢; omega)) (Fin.ext (by dsimp only at h ⊢; omega))
    · have h1 : min uv vv = vv := min_eq_right (by dsimp only at h; omega)
      have hm : min uv vv % 2 = 0 := by omega
      simp only [hm, ↓reduceIte]
      exact Prod.ext (Fin.ext (by dsimp only at h ⊢; omega)) (Fin.ext (by dsimp only at h ⊢; omega))

private lemma pathNEdges_fst_val (m : ℕ) (e : Fin m) :
    (pathNEdges m e).1.1.val = 2 * (e.val / 2) + 1 := by
  dsimp only [pathNEdges, pathNEdgeEnd]
  split_ifs <;> dsimp only <;> omega

private lemma pathNEdges_snd_val (m : ℕ) (e : Fin m) :
    (pathNEdges m e).1.2.val = if e.val = 0 then 0 else 2 * ((e.val - 1) / 2) + 2 := by
  dsimp only [pathNEdges, pathNEdgeEnd]
  split_ifs with he hz1 hz2
  · dsimp only; omega
  · dsimp only; omega
  · exfalso; omega
  · dsimp only
    have hq : 2 * (e.val / 2) + 1 = e.val := by omega
    have hq2 : (e.val - 1) / 2 = e.val / 2 := by omega
    omega

/-- Permutation on `Fin m` swapping pairs `(2j, 2j+1)` when `b j = true` (`2j+1 < m`). -/
def pathNP1Perm (m : ℕ) (b : Fin (m / 2) → Bool) : Equiv.Perm (Fin m) where
  toFun i :=
    if h : 2 * (i.val / 2) + 1 < m then
      if b ⟨i.val / 2, by omega⟩ = true then ⟨2 * (i.val / 2) + (1 - i.val % 2), by omega⟩ else i
    else i
  invFun i :=
    if h : 2 * (i.val / 2) + 1 < m then
      if b ⟨i.val / 2, by omega⟩ = true then ⟨2 * (i.val / 2) + (1 - i.val % 2), by omega⟩ else i
    else i
  left_inv i := by
    by_cases hm : 2 * (i.val / 2) + 1 < m
    · simp only [hm, ↓reduceDIte]
      by_cases hb : b ⟨i.val / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]
        have hm2 : 2 * ((2 * (i.val / 2) + (1 - i.val % 2)) / 2) + 1 < m := by omega
        have hidx : (⟨(2 * (i.val / 2) + (1 - i.val % 2)) / 2, by omega⟩ : Fin (m / 2)) =
            ⟨i.val / 2, by omega⟩ := Fin.ext (by dsimp only; omega)
        simp only [hm2, ↓reduceDIte, hidx, hb, ↓reduceIte]
        apply Fin.ext; dsimp only; omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, hm, ↓reduceDIte]
    · simp only [hm, ↓reduceDIte]
  right_inv i := by
    by_cases hm : 2 * (i.val / 2) + 1 < m
    · simp only [hm, ↓reduceDIte]
      by_cases hb : b ⟨i.val / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]
        have hm2 : 2 * ((2 * (i.val / 2) + (1 - i.val % 2)) / 2) + 1 < m := by omega
        have hidx : (⟨(2 * (i.val / 2) + (1 - i.val % 2)) / 2, by omega⟩ : Fin (m / 2)) =
            ⟨i.val / 2, by omega⟩ := Fin.ext (by dsimp only; omega)
        simp only [hm2, ↓reduceDIte, hidx, hb, ↓reduceIte]
        apply Fin.ext; dsimp only; omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, hm, ↓reduceDIte]
    · simp only [hm, ↓reduceDIte]

private def pathNP1Equiv (m : ℕ) : (Fin (m / 2) → Bool) ≃ bipP1 (pathGraphN (m + 1)) partEvenN where
  toFun b := ⟨Equiv.permCongr (pathNEdgeEquiv m) (pathNP1Perm m b), fun e => by
    obtain ⟨i, rfl⟩ := (pathNEdgeEquiv m).surjective e
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply Fin.ext
    change (pathNEdges m (pathNP1Perm m b i)).1.1.val = (pathNEdges m i).1.1.val
    rw [pathNEdges_fst_val, pathNEdges_fst_val]
    dsimp only [pathNP1Perm, Equiv.coe_fn_mk]
    by_cases hm : 2 * (i.val / 2) + 1 < m
    · simp only [hm, ↓reduceDIte]
      by_cases hb : b ⟨i.val / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]; omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    · simp only [hm, ↓reduceDIte]⟩
  invFun σ := fun j =>
    decide ((Equiv.permCongr (pathNEdgeEquiv m).symm σ.1) ⟨2 * j.val, by omega⟩ ≠ ⟨2 * j.val, by omega⟩)
  left_inv b := by
    funext j
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      pathNP1Perm, Equiv.coe_fn_mk]
    have hdv : (⟨2 * j.val, by omega⟩ : Fin m).val / 2 = j.val := by dsimp only; omega
    have hm : 2 * ((⟨2 * j.val, by omega⟩ : Fin m).val / 2) + 1 < m := by omega
    have hj_eq : (⟨(⟨2 * j.val, by omega⟩ : Fin m).val / 2, by omega⟩ : Fin (m / 2)) = j :=
      Fin.ext hdv
    simp only [hm, ↓reduceDIte, hj_eq]
    cases h : b j
    · simp
    · simp only [↓reduceIte, ne_eq, decide_eq_true_eq]
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    obtain ⟨i, rfl⟩ := (pathNEdgeEquiv m).surjective e
    let σ' := Equiv.permCongr (pathNEdgeEquiv m).symm σ.1
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change pathNEdges m (pathNP1Perm m _ i) = σ.1 (pathNEdges m i)
    suffices hsuff : pathNP1Perm m (fun j =>
        decide (σ' ⟨2 * j.val, by omega⟩ ≠ ⟨2 * j.val, by omega⟩)) i = σ' i by
      exact (congrArg (pathNEdges m) hsuff).trans ((pathNEdgeEquiv m).apply_symm_apply (σ.1 (pathNEdges m i)))
    have hdiv_eq : ∀ k : Fin m, (σ' k).val / 2 = k.val / 2 := fun k => by
      have hc' : σ' k = (pathNEdgeEquiv m).symm (σ.1 (pathNEdges m k)) := rfl
      have hback : pathNEdges m (σ' k) = σ.1 (pathNEdges m k) := by
        rw [hc']; exact (pathNEdgeEquiv m).apply_symm_apply _
      have hfv : (pathNEdges m (σ' k)).1.1.val = (pathNEdges m k).1.1.val := by
        rw [hback]; exact congrArg Fin.val (σ.2 (pathNEdges m k))
      rw [pathNEdges_fst_val, pathNEdges_fst_val] at hfv
      omega
    dsimp only [pathNP1Perm, Equiv.coe_fn_mk]
    by_cases hm : 2 * (i.val / 2) + 1 < m
    · simp only [hm, ↓reduceDIte]
      let j : Fin (m / 2) := ⟨i.val / 2, by omega⟩
      let i0 : Fin m := ⟨2 * j.val, by omega⟩
      let i1 : Fin m := ⟨2 * j.val + 1, by omega⟩
      have hdiv0 := hdiv_eq i0
      have hdiv1 := hdiv_eq i1
      have hjv : j.val = i.val / 2 := rfl
      have hi0v : i0.val = 2 * j.val := rfl
      have hi1v : i1.val = 2 * j.val + 1 := rfl
      have h0_cases : σ' i0 = i0 ∨ σ' i0 = i1 := by
        have hv : (σ' i0).val = 2 * j.val ∨ (σ' i0).val = 2 * j.val + 1 := by omega
        rcases hv with h | h
        · left; exact Fin.ext (by simp [i0]; exact h)
        · right; exact Fin.ext (by simp [i1]; exact h)
      have h1_cases : σ' i1 = i0 ∨ σ' i1 = i1 := by
        have hv : (σ' i1).val = 2 * j.val ∨ (σ' i1).val = 2 * j.val + 1 := by omega
        rcases hv with h | h
        · left; exact Fin.ext (by simp [i0]; exact h)
        · right; exact Fin.ext (by simp [i1]; exact h)
      have hne : σ' i0 ≠ σ' i1 := fun h => by
        have hv := congrArg Fin.val (σ'.injective h)
        simp [i0, i1] at hv
      have hi_cases : i = i0 ∨ i = i1 := by
        rcases (by omega : i.val = 2 * j.val ∨ i.val = 2 * j.val + 1) with h | h
        · left; exact Fin.ext (by simp [i0]; exact h)
        · right; exact Fin.ext (by simp [i1]; exact h)
      change (if decide (σ' i0 ≠ i0) = true then ⟨2 * (i.val / 2) + (1 - i.val % 2), _⟩ else i) = σ' i
      rcases h0_cases with hfix0 | hswap0
      · have hfix1 : σ' i1 = i1 := by
          rcases h1_cases with h | h
          · exact absurd (hfix0.trans h.symm) hne
          · exact h
        simp only [hfix0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        rcases hi_cases with hi0 | hi1
        · rw [hi0]; exact hfix0.symm
        · rw [hi1]; exact hfix1.symm
      · have hswap1 : σ' i1 = i0 := by
          rcases h1_cases with h | h
          · exact h
          · exact absurd (hswap0.trans h.symm) hne
        have hswap_ne : σ' i0 ≠ i0 := fun h => hne (h.trans hswap1.symm)
        simp only [hswap_ne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
        apply Fin.ext; dsimp only
        rcases hi_cases with hi0 | hi1
        · have hv : (σ' i).val = (σ' i0).val := congrArg (fun k => (σ' k).val) hi0
          have hv0 : (σ' i0).val = i1.val := congrArg Fin.val hswap0
          have hvi : i.val = i0.val := congrArg Fin.val hi0
          omega
        · have hv : (σ' i).val = (σ' i1).val := congrArg (fun k => (σ' k).val) hi1
          have hv1 : (σ' i1).val = i0.val := congrArg Fin.val hswap1
          have hvi : i.val = i1.val := congrArg Fin.val hi1
          omega
    · simp only [hm, ↓reduceDIte]
      have hdivi := hdiv_eq i
      have hlt := (σ' i).isLt
      exact Fin.ext (by omega)

/-- Permutation on `Fin m` swapping pairs `(2j+1, 2j+2)` when `b j = true` (`2j+2 < m`). -/
def pathNP2Perm (m : ℕ) (b : Fin ((m - 1) / 2) → Bool) : Equiv.Perm (Fin m) where
  toFun i :=
    if h : 0 < i.val ∧ 2 * ((i.val - 1) / 2) + 2 < m then
      if b ⟨(i.val - 1) / 2, by omega⟩ = true then
        ⟨2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2), by omega⟩
      else i
    else i
  invFun i :=
    if h : 0 < i.val ∧ 2 * ((i.val - 1) / 2) + 2 < m then
      if b ⟨(i.val - 1) / 2, by omega⟩ = true then
        ⟨2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2), by omega⟩
      else i
    else i
  left_inv i := by
    by_cases h1 : 0 < i.val ∧ 2 * ((i.val - 1) / 2) + 2 < m
    · simp only [h1.1, h1.2, and_self, ↓reduceDIte]
      by_cases hb : b ⟨(i.val - 1) / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]
        have h2 : 0 < 2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2) ∧
            2 * (((2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2)) - 1) / 2) + 2 < m :=
          ⟨by omega, by omega⟩
        have hidx : (⟨((2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2)) - 1) / 2, by omega⟩ :
            Fin ((m - 1) / 2)) = ⟨(i.val - 1) / 2, by omega⟩ := Fin.ext (by dsimp only; omega)
        simp only [h2.1, h2.2, and_self, ↓reduceDIte, hidx, hb, ↓reduceIte]
        apply Fin.ext; dsimp only; omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, h1.1, h1.2, and_self, ↓reduceDIte]
    · simp only [h1, ↓reduceDIte]
  right_inv i := by
    by_cases h1 : 0 < i.val ∧ 2 * ((i.val - 1) / 2) + 2 < m
    · simp only [h1.1, h1.2, and_self, ↓reduceDIte]
      by_cases hb : b ⟨(i.val - 1) / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]
        have h2 : 0 < 2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2) ∧
            2 * (((2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2)) - 1) / 2) + 2 < m :=
          ⟨by omega, by omega⟩
        have hidx : (⟨((2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2)) - 1) / 2, by omega⟩ :
            Fin ((m - 1) / 2)) = ⟨(i.val - 1) / 2, by omega⟩ := Fin.ext (by dsimp only; omega)
        simp only [h2.1, h2.2, and_self, ↓reduceDIte, hidx, hb, ↓reduceIte]
        apply Fin.ext; dsimp only; omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, h1.1, h1.2, and_self, ↓reduceDIte]
    · simp only [h1, ↓reduceDIte]

private def pathNP2Equiv (m : ℕ) : (Fin ((m - 1) / 2) → Bool) ≃ bipP2 (pathGraphN (m + 1)) partEvenN where
  toFun b := ⟨Equiv.permCongr (pathNEdgeEquiv m) (pathNP2Perm m b), fun e => by
    obtain ⟨i, rfl⟩ := (pathNEdgeEquiv m).surjective e
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply Fin.ext
    change (pathNEdges m (pathNP2Perm m b i)).1.2.val = (pathNEdges m i).1.2.val
    rw [pathNEdges_snd_val, pathNEdges_snd_val]
    dsimp only [pathNP2Perm, Equiv.coe_fn_mk]
    by_cases h1 : 0 < i.val ∧ 2 * ((i.val - 1) / 2) + 2 < m
    · simp only [h1.1, h1.2, and_self, ↓reduceDIte]
      by_cases hb : b ⟨(i.val - 1) / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]
        have hk0 : ¬ (2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2) = 0) := by omega
        have hi0 : ¬ (i.val = 0) := by omega
        simp only [hk0, hi0, ↓reduceIte]
        omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    · simp only [h1, ↓reduceDIte]⟩
  invFun σ := fun j =>
    decide ((Equiv.permCongr (pathNEdgeEquiv m).symm σ.1) ⟨2 * j.val + 1, by omega⟩ ≠ ⟨2 * j.val + 1, by omega⟩)
  left_inv b := by
    funext j
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      pathNP2Perm, Equiv.coe_fn_mk]
    have h1 : 0 < (⟨2 * j.val + 1, by omega⟩ : Fin m).val ∧
        2 * (((⟨2 * j.val + 1, by omega⟩ : Fin m).val - 1) / 2) + 2 < m :=
      ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hidx : (⟨((⟨2 * j.val + 1, by omega⟩ : Fin m).val - 1) / 2, by omega⟩ :
        Fin ((m - 1) / 2)) = j := Fin.ext (by dsimp only; omega)
    simp only [h1.1, h1.2, and_self, ↓reduceDIte, hidx]
    cases h : b j
    · simp
    · simp only [↓reduceIte, ne_eq, decide_eq_true_eq]
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
  right_inv σ := by
    apply Subtype.ext; apply Equiv.ext; intro e
    obtain ⟨i, rfl⟩ := (pathNEdgeEquiv m).surjective e
    let σ' := Equiv.permCongr (pathNEdgeEquiv m).symm σ.1
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change pathNEdges m (pathNP2Perm m _ i) = σ.1 (pathNEdges m i)
    suffices hsuff : pathNP2Perm m (fun j =>
        decide (σ' ⟨2 * j.val + 1, by omega⟩ ≠ ⟨2 * j.val + 1, by omega⟩)) i = σ' i by
      exact (congrArg (pathNEdges m) hsuff).trans ((pathNEdgeEquiv m).apply_symm_apply (σ.1 (pathNEdges m i)))
    have hsnd_val : ∀ k : Fin m, (pathNEdges m (σ' k)).1.2.val = (pathNEdges m k).1.2.val := fun k => by
      have hc' : σ' k = (pathNEdgeEquiv m).symm (σ.1 (pathNEdges m k)) := rfl
      have hback : pathNEdges m (σ' k) = σ.1 (pathNEdges m k) := by
        rw [hc']; exact (pathNEdgeEquiv m).apply_symm_apply _
      rw [hback]
      exact congrArg Fin.val (σ.2 (pathNEdges m k))
    have hfix0 : (∀ h0 : 0 < m, σ' ⟨0, h0⟩ = ⟨0, h0⟩) := fun h0 => by
      have h := hsnd_val ⟨0, h0⟩
      rw [pathNEdges_snd_val, pathNEdges_snd_val] at h
      simp only [↓reduceIte] at h
      by_cases hz : (σ' ⟨0, h0⟩).val = 0
      · exact Fin.ext hz
      · simp only [hz, ↓reduceIte] at h; exfalso; omega
    have hpair : ∀ k : Fin m, 0 < k.val →
        0 < (σ' k).val ∧ ((σ' k).val - 1) / 2 = (k.val - 1) / 2 := fun k hkpos => by
      have h := hsnd_val k
      rw [pathNEdges_snd_val, pathNEdges_snd_val] at h
      have hk0 : k.val ≠ 0 := by omega
      simp only [hk0, ↓reduceIte] at h
      by_cases hσ0 : (σ' k).val = 0
      · simp only [hσ0, ↓reduceIte] at h; exfalso; omega
      · simp only [hσ0, ↓reduceIte] at h; exact ⟨by omega, by omega⟩
    dsimp only [pathNP2Perm, Equiv.coe_fn_mk]
    by_cases h1 : 0 < i.val ∧ 2 * ((i.val - 1) / 2) + 2 < m
    · simp only [h1.1, h1.2, and_self, ↓reduceDIte]
      let j : Fin ((m - 1) / 2) := ⟨(i.val - 1) / 2, by omega⟩
      let i0 : Fin m := ⟨2 * j.val + 1, by omega⟩
      let i1 : Fin m := ⟨2 * j.val + 2, by omega⟩
      have hjv : j.val = (i.val - 1) / 2 := rfl
      have hi0v : i0.val = 2 * j.val + 1 := rfl
      have hi1v : i1.val = 2 * j.val + 2 := rfl
      have hp0 := hpair i0 (by omega)
      have hp1 := hpair i1 (by omega)
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
      change (if decide (σ' i0 ≠ i0) = true then
          ⟨2 * ((i.val - 1) / 2) + 1 + (1 - (i.val - 1) % 2), _⟩ else i) = σ' i
      rcases hcases0 with hfix0' | hswap0
      · have hfix1' : σ' i1 = i1 := by
          rcases hcases1 with h | h
          · exact absurd (hfix0'.trans h.symm) hne
          · exact h
        simp only [hfix0', ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        rcases hi_cases with hi0 | hi1
        · rw [hi0]; exact hfix0'.symm
        · rw [hi1]; exact hfix1'.symm
      · have hswap1 : σ' i1 = i0 := by
          rcases hcases1 with h | h
          · exact h
          · exact absurd (hswap0.trans h.symm) hne
        have hswap_ne : σ' i0 ≠ i0 := fun h => hne (h.trans hswap1.symm)
        simp only [hswap_ne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
        apply Fin.ext; dsimp only
        rcases hi_cases with hi0 | hi1
        · have hv : (σ' i).val = (σ' i0).val := congrArg (fun k => (σ' k).val) hi0
          have hv0 : (σ' i0).val = i1.val := congrArg Fin.val hswap0
          have hvi : i.val = i0.val := congrArg Fin.val hi0
          omega
        · have hv : (σ' i).val = (σ' i1).val := congrArg (fun k => (σ' k).val) hi1
          have hv1 : (σ' i1).val = i0.val := congrArg Fin.val hswap1
          have hvi : i.val = i1.val := congrArg Fin.val hi1
          omega
    · simp only [h1, ↓reduceDIte]
      by_cases hi0 : i.val = 0
      · have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
        have hi_eq : i = ⟨0, hm_pos⟩ := Fin.ext hi0
        have hself : σ' i = i := (congrArg σ' hi_eq).trans ((hfix0 hm_pos).trans hi_eq.symm)
        exact hself.symm
      · have hpi := hpair i (by omega)
        have hlt := (σ' i).isLt
        exact Fin.ext (by omega)

end PathGraphNDef

/-! ## Part 2: Spinor Inner-Product Peeling Recurrence & $\mathrm{SU}(2)$ Hyperbolic Norm Identity -/

section SpinorPathRecurrence

private lemma fin2_eq' (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

/-- Hermitian spinor inner product $\langle u, v \rangle = \overline{u_0}v_0 + \overline{u_1}v_1$. -/
def spIn (u v : Fin 2 → ℂ) : ℂ :=
  starRingEnd ℂ (u 0) * v 0 + starRingEnd ℂ (u 1) * v 1

lemma spIn_self_unit {u : Fin 2 → ℂ} (hu : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1) : spIn u u = 1 := by
  have hsq : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc spIn u u = ((‖u 0‖ ^ 2 : ℝ) : ℂ) + ((‖u 1‖ ^ 2 : ℝ) : ℂ) := by
        simp only [spIn, hsq]
    _ = ((‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    _ = 1 := by rw [hu, Complex.ofReal_one]

lemma jTilde_unit {u : Fin 2 → ℂ} (hu : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1) :
    ‖jTilde u 0‖ ^ 2 + ‖jTilde u 1‖ ^ 2 = 1 := by
  simp only [jTilde, norm_neg, Complex.norm_conj]
  linarith [hu]

lemma spIn_ortho_basis {prev φ : Fin 2 → ℂ} (hp : ‖prev 0‖ ^ 2 + ‖prev 1‖ ^ 2 = 1)
    (hφ : ‖φ 0‖ ^ 2 + ‖φ 1‖ ^ 2 = 1) :
    ‖spIn prev φ‖ ^ 2 + ‖spIn (jTilde prev) φ‖ ^ 2 = 1 := by
  have hsp1 : (starRingEnd ℂ (prev 0) * φ 0 + starRingEnd ℂ (prev 1) * φ 1) *
      starRingEnd ℂ (starRingEnd ℂ (prev 0) * φ 0 + starRingEnd ℂ (prev 1) * φ 1) +
      (starRingEnd ℂ (-starRingEnd ℂ (prev 1)) * φ 0 + starRingEnd ℂ (starRingEnd ℂ (prev 0)) * φ 1) *
      starRingEnd ℂ (starRingEnd ℂ (-starRingEnd ℂ (prev 1)) * φ 0 + starRingEnd ℂ (starRingEnd ℂ (prev 0)) * φ 1) =
      (prev 0 * starRingEnd ℂ (prev 0) + prev 1 * starRingEnd ℂ (prev 1)) *
      (φ 0 * starRingEnd ℂ (φ 0) + φ 1 * starRingEnd ℂ (φ 1)) := by
    simp only [map_add, map_mul, map_neg, Complex.conj_conj]
    ring
  have hsqC : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hC : spIn prev φ * starRingEnd ℂ (spIn prev φ) +
      spIn (jTilde prev) φ * starRingEnd ℂ (spIn (jTilde prev) φ) = 1 := by
    calc spIn prev φ * starRingEnd ℂ (spIn prev φ) +
          spIn (jTilde prev) φ * starRingEnd ℂ (spIn (jTilde prev) φ)
        = (prev 0 * starRingEnd ℂ (prev 0) + prev 1 * starRingEnd ℂ (prev 1)) *
            (φ 0 * starRingEnd ℂ (φ 0) + φ 1 * starRingEnd ℂ (φ 1)) := by
          simpa only [spIn, jTilde] using hsp1
      _ = ((‖prev 0‖ ^ 2 + ‖prev 1‖ ^ 2 : ℝ) : ℂ) * ((‖φ 0‖ ^ 2 + ‖φ 1‖ ^ 2 : ℝ) : ℂ) := by
          rw [hsqC, hsqC, hsqC, hsqC]; push_cast; rfl
      _ = 1 := by rw [hp, hφ, Complex.ofReal_one, one_mul]
  rw [hsqC, hsqC] at hC
  exact_mod_cast hC

lemma spIn_add_smul_left (a b : ℂ) (φ ψ x : Fin 2 → ℂ) :
    spIn (fun k => a * φ k + b * ψ k) x =
      starRingEnd ℂ a * spIn φ x + starRingEnd ℂ b * spIn ψ x := by
  simp only [spIn, map_add, map_mul]
  ring

lemma spIn_add_smul_right (a b : ℂ) (x φ ψ : Fin 2 → ℂ) :
    spIn x (fun k => a * φ k + b * ψ k) =
      a * spIn x φ + b * spIn x ψ := by
  simp only [spIn]
  ring

lemma spIn_basis_expand {prev : Fin 2 → ℂ} (hp : ‖prev 0‖ ^ 2 + ‖prev 1‖ ^ 2 = 1)
    (w : Fin 2 → ℂ) :
    w = fun k => spIn prev w * prev k + spIn (jTilde prev) w * jTilde prev k := by
  have hdet1 : prev 0 * starRingEnd ℂ (prev 0) + prev 1 * starRingEnd ℂ (prev 1) = 1 := by
    have hsqC : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsqC, hsqC]
    exact_mod_cast hp
  ext k
  rcases fin2_eq' k with rfl | rfl <;>
    simp only [spIn, jTilde, Complex.conj_conj, map_neg]
  · calc w 0 = 1 * w 0 := (one_mul _).symm
      _ = (prev 0 * starRingEnd ℂ (prev 0) + prev 1 * starRingEnd ℂ (prev 1)) * w 0 := by rw [hdet1]
      _ = _ := by ring
  · calc w 1 = 1 * w 1 := (one_mul _).symm
      _ = (prev 0 * starRingEnd ℂ (prev 0) + prev 1 * starRingEnd ℂ (prev 1)) * w 1 := by rw [hdet1]
      _ = _ := by ring

lemma spIn_flip_jTilde_right {prev φ : Fin 2 → ℂ} (hp : ‖prev 0‖ ^ 2 + ‖prev 1‖ ^ 2 = 1) :
    spIn (jTilde φ) prev = -spIn (jTilde prev) φ := by
  have _ := hp
  simp only [spIn, jTilde, Complex.conj_conj, map_neg]
  ring

/-- **Exact Unified $\mathrm{SU}(2)$ Hyperbolic Step Identity:**
Whenever `‖U‖ ^ 2 + ‖V‖ ^ 2 = 1`, setting `d = U*a + V*β`, `c = -conj V * a + conj U * β`,
`a' = a + conj U * d`, and `β' = -V * d` satisfies
`(‖a'‖^2 - ‖β'‖^2) - (‖a‖^2 - ‖β‖^2) = ‖U‖^2 * (3 * ‖d‖^2 + ‖c‖^2) ≥ 0`. -/
lemma hyperbolic_step_id (a β U V : ℂ) (hUV : ‖U‖ ^ 2 + ‖V‖ ^ 2 = 1) :
    let d := U * a + V * β
    let c := -starRingEnd ℂ V * a + starRingEnd ℂ U * β
    let a' := a + starRingEnd ℂ U * d
    let β' := -V * d
    (‖a'‖ ^ 2 - ‖β'‖ ^ 2) - (‖a‖ ^ 2 - ‖β‖ ^ 2) = ‖U‖ ^ 2 * (3 * ‖d‖ ^ 2 + ‖c‖ ^ 2) := by
  intro d c a' β'
  have hUVC : U * starRingEnd ℂ U + V * starRingEnd ℂ V = 1 := by
    have hsqC : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsqC, hsqC]
    exact_mod_cast hUV
  have ha_id : a = starRingEnd ℂ U * d - V * c := by
    calc a = (U * starRingEnd ℂ U + V * starRingEnd ℂ V) * a := by rw [hUVC, one_mul]
      _ = starRingEnd ℂ U * (U * a + V * β) - V * (-starRingEnd ℂ V * a + starRingEnd ℂ U * β) := by ring
      _ = starRingEnd ℂ U * d - V * c := rfl
  have hβ_id : β = starRingEnd ℂ V * d + U * c := by
    calc β = (U * starRingEnd ℂ U + V * starRingEnd ℂ V) * β := by rw [hUVC, one_mul]
      _ = starRingEnd ℂ V * (U * a + V * β) + U * (-starRingEnd ℂ V * a + starRingEnd ℂ U * β) := by ring
      _ = starRingEnd ℂ V * d + U * c := rfl
  have ha'_id : a' = 2 * starRingEnd ℂ U * d - V * c := by
    calc a' = (starRingEnd ℂ U * d - V * c) + starRingEnd ℂ U * d := by rw [← ha_id]
      _ = 2 * starRingEnd ℂ U * d - V * c := by ring
  have hidentC : (a' * starRingEnd ℂ a' - β' * starRingEnd ℂ β') -
      (a * starRingEnd ℂ a - β * starRingEnd ℂ β) =
      (U * starRingEnd ℂ U) * (3 * (d * starRingEnd ℂ d) + c * starRingEnd ℂ c) := by
    rw [ha'_id, ha_id, hβ_id]
    dsimp only [β']
    simp only [map_add, map_sub, map_mul, map_neg, Complex.conj_conj, map_ofNat]
    ring
  have hsqC : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsqC, hsqC, hsqC, hsqC, hsqC, hsqC, hsqC] at hidentC
  exact_mod_cast hidentC

/-- Cast equivalence splitting `(Fin m → Bool)` into `(Fin n → Bool) × Bool` when `m = n + 1`. -/
private def boolSnocCast {m n : ℕ} (h : m = n + 1) : (Fin n → Bool) × Bool ≃ (Fin m → Bool) where
  toFun p j := if hj : j.val < n then p.1 ⟨j.val, hj⟩ else p.2
  invFun f := (fun j => f ⟨j.val, by omega⟩, f ⟨n, by omega⟩)
  left_inv p := by
    ext j
    · simp [j.isLt]
    · have hn : ¬ n < n := lt_irrefl n
      change (if hj : (⟨n, by omega⟩ : Fin m).val < n then p.1 ⟨_, hj⟩ else p.2) = p.2
      simp only [hn, ↓reduceDIte]
  right_inv f := by
    funext j
    have hjt : j.val < m := j.isLt
    by_cases hj : j.val < n
    · simp [hj]
    · have hjn : (⟨n, by omega⟩ : Fin m) = j := Fin.ext (by dsimp only; omega)
      simp [hj, hjn]

/-- Total path Gram sum for `k` edges `0 .. k - 1`. -/
noncomputable def pathGramSum (k : ℕ) (Φ : ℕ → Fin 2 → ℂ) : ℂ :=
  ∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k - 1) / 2) → Bool,
    ∏ e : Fin k, spIn (Φ (pathNP1Perm k b₁ e).val) (Φ (pathNP2Perm k b₂ e).val)

/-- Open-boundary path Gram sum for `k` edges (`k ≥ 1`), replacing the fixed endpoint spinor
at the last edge `e = k - 1` (`pathNP1Perm` side when `k` is odd, `pathNP2Perm` side when `k` is even)
with arbitrary `x : Fin 2 → ℂ`. -/
noncomputable def pathEndSum (k : ℕ) (Φ : ℕ → Fin 2 → ℂ) (x : Fin 2 → ℂ) : ℂ :=
  ∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k - 1) / 2) → Bool,
    ∏ e : Fin k,
      let j1 := (pathNP1Perm k b₁ e).val
      let j2 := (pathNP2Perm k b₂ e).val
      if e.val + 1 = k then
        if k % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
      else spIn (Φ j1) (Φ j2)

lemma pathEndSum_self (k : ℕ) (hk : 1 ≤ k) (Φ : ℕ → Fin 2 → ℂ) :
    pathEndSum k Φ (Φ (k - 1)) = pathGramSum k Φ := by
  unfold pathEndSum pathGramSum
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases he : e.val + 1 = k
  · have hfix1 : k % 2 = 1 → (pathNP1Perm k b₁ e).val = k - 1 := fun hm => by
      dsimp only [pathNP1Perm, Equiv.coe_fn_mk]
      have hnt : ¬ (2 * (e.val / 2) + 1 < k) := by omega
      simp [hnt]; omega
    have hfix2 : k % 2 ≠ 1 → (pathNP2Perm k b₂ e).val = k - 1 := fun hm => by
      dsimp only [pathNP2Perm, Equiv.coe_fn_mk]
      have hnt : ¬ (0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k) := by omega
      simp [hnt]; omega
    by_cases hm : k % 2 = 1
    · simp only [he, hm, ↓reduceIte, hfix1 hm]
    · simp only [he, hm, ↓reduceIte, hfix2 hm]
  · simp [he]

private lemma pathNP1Perm_castSucc_odd {k : ℕ} (hk1 : k % 2 = 1) (_hk : 1 ≤ k)
    (b₁ : Fin (k / 2) → Bool) (last : Bool) (e : Fin k) :
    (pathNP1Perm (k + 1) (boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last))
        e.castSucc).val =
      if last = true ∧ e.val + 1 = k then k else (pathNP1Perm k b₁ e).val := by
  dsimp only [pathNP1Perm, Equiv.coe_fn_mk]
  by_cases he : e.val + 1 = k
  · have hm_succ : 2 * (e.castSucc.val / 2) + 1 < k + 1 := by
      simp only [Fin.val_castSucc]; omega
    have hm_k : ¬ (2 * (e.val / 2) + 1 < k) := by omega
    have hb_eq : boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last)
        ⟨e.castSucc.val / 2, by omega⟩ = last := by
      dsimp only [boolSnocCast, Equiv.coe_fn_mk]
      rw [dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_castSucc]; omega))]
    rw [dite_eq_left_of_eq_true (eq_true hm_succ), dite_eq_right_of_eq_false (eq_false hm_k)]
    simp only [hb_eq]
    by_cases hlast : last = true
    · simp only [hlast, ↓reduceIte, he, and_self]
      dsimp only [Fin.val_castSucc]; omega
    · simp only [hlast, Bool.false_eq_true, ↓reduceIte, false_and]
      rfl
  · by_cases hm_k : 2 * (e.val / 2) + 1 < k
    · have hm_succ : 2 * (e.castSucc.val / 2) + 1 < k + 1 := by
        simp only [Fin.val_castSucc]; omega
      have hb_eq : boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last)
          ⟨e.castSucc.val / 2, by omega⟩ = b₁ ⟨e.val / 2, by omega⟩ := by
        dsimp only [boolSnocCast, Equiv.coe_fn_mk]
        rw [dite_eq_left_of_eq_true (eq_true (by simp only [Fin.val_castSucc]; omega))]
        exact congrArg b₁ (Fin.ext (by simp only [Fin.val_castSucc]))
      simp only [hm_succ, hm_k, ↓reduceDIte, hb_eq, he, and_false, ↓reduceIte]
      by_cases hb : b₁ ⟨e.val / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte]; rfl
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]; rfl
    · have hm_succ : ¬ (2 * (e.castSucc.val / 2) + 1 < k + 1) := by
        simp only [Fin.val_castSucc]; omega
      simp only [hm_succ, hm_k, ↓reduceDIte, he, and_false, ↓reduceIte]
      rfl

private lemma pathNP2Perm_castSucc_odd {k : ℕ} (hk1 : k % 2 = 1)
    (b₂ : Fin (k / 2) → Bool) (e : Fin k) :
    (pathNP2Perm (k + 1) (fun j => b₂ ⟨j.val, by omega⟩) e.castSucc).val =
      (pathNP2Perm k (fun j => b₂ ⟨j.val, by omega⟩) e).val := by
  dsimp only [pathNP2Perm, Equiv.coe_fn_mk]
  have hiff : (0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1) ↔
      (0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k) := by
    simp only [Fin.val_castSucc]; omega
  by_cases h1 : 0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k
  · have h2 : 0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1 := hiff.mpr h1
    have hbit : b₂ ⟨(e.castSucc.val - 1) / 2, by omega⟩ = b₂ ⟨(e.val - 1) / 2, by omega⟩ :=
      congrArg b₂ (Fin.ext (by simp only [Fin.val_castSucc]))
    simp only [h1.1, h1.2, h2.1, h2.2, and_self, ↓reduceDIte, hbit]
    by_cases hb : b₂ ⟨(e.val - 1) / 2, by omega⟩ = true
    · simp only [hb, ↓reduceIte, Fin.val_castSucc]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rfl
  · have h2 : ¬ (0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1) :=
      fun hc => h1 (hiff.mp hc)
    simp only [h1, h2, ↓reduceDIte]
    rfl

private lemma pathNP1Perm_castSucc_even {k : ℕ} (hk0 : k % 2 = 0)
    (b₁ : Fin (k / 2) → Bool) (e : Fin k) :
    (pathNP1Perm (k + 1) (fun j => b₁ ⟨j.val, by omega⟩) e.castSucc).val =
      (pathNP1Perm k b₁ e).val := by
  dsimp only [pathNP1Perm, Equiv.coe_fn_mk]
  have hiff : 2 * (e.castSucc.val / 2) + 1 < k + 1 ↔ 2 * (e.val / 2) + 1 < k := by
    simp only [Fin.val_castSucc]; omega
  by_cases h1 : 2 * (e.val / 2) + 1 < k
  · have h2 : 2 * (e.castSucc.val / 2) + 1 < k + 1 := hiff.mpr h1
    have hbit : b₁ ⟨e.castSucc.val / 2, by omega⟩ = b₁ ⟨e.val / 2, by omega⟩ :=
      congrArg b₁ (Fin.ext (by simp only [Fin.val_castSucc]))
    simp only [h1, h2, ↓reduceDIte, hbit]
    by_cases hb : b₁ ⟨e.val / 2, by omega⟩ = true
    · simp only [hb, ↓reduceIte, Fin.val_castSucc]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rfl
  · have h2 : ¬ (2 * (e.castSucc.val / 2) + 1 < k + 1) := fun hc => h1 (hiff.mp hc)
    simp only [h1, h2, ↓reduceDIte]
    rfl

private lemma pathNP2Perm_castSucc_even {k : ℕ} (hk0 : k % 2 = 0) (hk : 2 ≤ k)
    (b₂ : Fin ((k - 1) / 2) → Bool) (last : Bool) (e : Fin k) :
    (pathNP2Perm (k + 1) (boolSnocCast (by omega : k / 2 = (k - 1) / 2 + 1) (b₂, last))
        e.castSucc).val =
      if last = true ∧ e.val + 1 = k then k else (pathNP2Perm k b₂ e).val := by
  dsimp only [pathNP2Perm, Equiv.coe_fn_mk]
  by_cases he : e.val + 1 = k
  · have hm_succ : 0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1 := by
      simp only [Fin.val_castSucc]; omega
    have hm_k : ¬ (0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k) := by omega
    have hb_eq : boolSnocCast (by omega : k / 2 = (k - 1) / 2 + 1) (b₂, last)
        ⟨(e.castSucc.val - 1) / 2, by omega⟩ = last := by
      dsimp only [boolSnocCast, Equiv.coe_fn_mk]
      simp only [(by simp only [Fin.val_castSucc]; omega : ¬ (e.castSucc.val - 1) / 2 < (k - 1) / 2), ↓reduceDIte]
    simp only [hm_succ.1, hm_succ.2, and_self, hm_k, ↓reduceDIte, hb_eq]
    by_cases hlast : last = true
    · simp only [hlast, ↓reduceIte, he, and_self]
      dsimp only [Fin.val_castSucc]; omega
    · simp only [hlast, Bool.false_eq_true, ↓reduceIte, false_and]
      rfl
  · by_cases hm_k : 0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k
    · have hm_succ : 0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1 := by
        simp only [Fin.val_castSucc]; omega
      have hb_eq : boolSnocCast (by omega : k / 2 = (k - 1) / 2 + 1) (b₂, last)
          ⟨(e.castSucc.val - 1) / 2, by omega⟩ = b₂ ⟨(e.val - 1) / 2, by omega⟩ := by
        dsimp only [boolSnocCast, Equiv.coe_fn_mk]
        simp only [(by simp only [Fin.val_castSucc]; omega : (e.castSucc.val - 1) / 2 < (k - 1) / 2), ↓reduceDIte]
        exact congrArg b₂ (Fin.ext (by simp only [Fin.val_castSucc]))
      simp only [hm_succ.1, hm_succ.2, hm_k.1, hm_k.2, and_self, ↓reduceDIte, hb_eq, he, and_false, ↓reduceIte]
      by_cases hb : b₂ ⟨(e.val - 1) / 2, by omega⟩ = true
      · simp only [hb, ↓reduceIte, Fin.val_castSucc]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rfl
    · have hm_succ : ¬ (0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1) := by
        simp only [Fin.val_castSucc]; omega
      simp only [hm_succ, hm_k, ↓reduceDIte, he, and_false, ↓reduceIte]
      rfl

private def boolCastEquiv {m₁ m₂ : ℕ} (h : m₁ = m₂) : (Fin m₁ → Bool) ≃ (Fin m₂ → Bool) where
  toFun f j := f ⟨j.val, by omega⟩
  invFun g j := g ⟨j.val, by omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma pathNP1Perm_last_odd {k : ℕ} (hk1 : k % 2 = 1)
    (b₁ : Fin (k / 2) → Bool) (last : Bool) :
    (pathNP1Perm (k + 1) (boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last))
        (Fin.last k)).val =
      if last = true then k - 1 else k := by
  dsimp only [pathNP1Perm, Equiv.coe_fn_mk, Fin.val_last]
  have hm : 2 * (k / 2) + 1 < k + 1 := by omega
  have hb : boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last)
      ⟨k / 2, by omega⟩ = last := by
    dsimp only [boolSnocCast, Equiv.coe_fn_mk]
    rw [dite_eq_right_of_eq_false (eq_false (by omega))]
  simp only [hm, ↓reduceDIte, hb]
  by_cases hlast : last = true
  · simp only [hlast, ↓reduceIte]; omega
  · simp only [hlast, Bool.false_eq_true, ↓reduceIte, Fin.val_last]

private lemma pathNP2Perm_last_even {k : ℕ} (hk0 : k % 2 = 0) (hk : 2 ≤ k)
    (b₂ : Fin ((k - 1) / 2) → Bool) (last : Bool) :
    (pathNP2Perm (k + 1) (boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last))
        (Fin.last k)).val =
      if last = true then k - 1 else k := by
  dsimp only [pathNP2Perm, Equiv.coe_fn_mk, Fin.val_last]
  have hm : 0 < k ∧ 2 * ((k - 1) / 2) + 2 < k + 1 := ⟨by omega, by omega⟩
  have hb : boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
      ⟨(k - 1) / 2, by omega⟩ = last := by
    dsimp only [boolSnocCast, Equiv.coe_fn_mk]
    rw [dite_eq_right_of_eq_false (eq_false (by omega))]
  simp only [hm.1, hm.2, and_self, ↓reduceDIte, hb]
  by_cases hlast : last = true
  · simp only [hlast, ↓reduceIte]; omega
  · simp only [hlast, Bool.false_eq_true, ↓reduceIte, Fin.val_last]

/-- One-edge open-boundary peeling recurrence for both parities of `k ≥ 1`. -/
theorem pathEndSum_succ (k : ℕ) (hk : 1 ≤ k) (Φ : ℕ → Fin 2 → ℂ) (x : Fin 2 → ℂ) :
    pathEndSum (k + 1) Φ x =
      if k % 2 = 1 then
        pathEndSum k Φ (Φ (k - 1)) * spIn (Φ k) x + pathEndSum k Φ (Φ k) * spIn (Φ (k - 1)) x
      else
        pathEndSum k Φ (Φ (k - 1)) * spIn x (Φ k) + pathEndSum k Φ (Φ k) * spIn x (Φ (k - 1)) := by
  by_cases hk1 : k % 2 = 1
  · simp only [hk1, ↓reduceIte]
    have hkmod : ¬ ((k + 1) % 2 = 1) := by omega
    unfold pathEndSum
    have hbranch : ∀ (last : Bool),
        (∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last)
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂ e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2)) =
        (∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k - 1) / 2) → Bool,
          ∏ e : Fin k,
            let j1 := (pathNP1Perm k b₁ e).val
            let j2 := (pathNP2Perm k b₂ e).val
            if e.val + 1 = k then spIn (Φ (if last = true then k else k - 1)) (Φ j2)
            else spIn (Φ j1) (Φ j2)) *
          spIn (Φ (if last = true then k - 1 else k)) x := by
      intro last
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b₁ _ => ?_
      rw [Finset.sum_mul]
      rw [← Fintype.sum_equiv (boolCastEquiv (by omega : (k + 1 - 1) / 2 = (k - 1) / 2))
        (fun b₂ => ∏ e : Fin (k + 1),
          let b₁' := boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last)
          let j1 := (pathNP1Perm (k + 1) b₁' e).val
          let j2 := (pathNP2Perm (k + 1) b₂ e).val
          if e.val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2))
        (fun b₂ => (∏ e : Fin k,
          let j1 := (pathNP1Perm k b₁ e).val
          let j2 := (pathNP2Perm k b₂ e).val
          if e.val + 1 = k then spIn (Φ (if last = true then k else k - 1)) (Φ j2)
          else spIn (Φ j1) (Φ j2)) *
          spIn (Φ (if last = true then k - 1 else k)) x)
        (fun b₂ => by
          rw [Fin.prod_univ_castSucc]
          have hlast : (let b₁' := boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last)
              let j1 := (pathNP1Perm (k + 1) b₁' (Fin.last k)).val
              let j2 := (pathNP2Perm (k + 1) b₂ (Fin.last k)).val
              if (Fin.last k).val + 1 = k + 1 then
                if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
              else spIn (Φ j1) (Φ j2)) =
              spIn (Φ (if last = true then k - 1 else k)) x := by
            simp only [Fin.val_last, ↓reduceIte, hkmod, pathNP1Perm_last_odd hk1 b₁ last]
          have hrest : (∏ e : Fin k,
              let b₁' := boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) (b₁, last)
              let j1 := (pathNP1Perm (k + 1) b₁' e.castSucc).val
              let j2 := (pathNP2Perm (k + 1) b₂ e.castSucc).val
              if e.castSucc.val + 1 = k + 1 then
                if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
              else spIn (Φ j1) (Φ j2)) =
              ∏ e : Fin k,
                let j1 := (pathNP1Perm k b₁ e).val
                let j2 := (pathNP2Perm k (boolCastEquiv (by omega : (k + 1 - 1) / 2 = (k - 1) / 2) b₂) e).val
                if e.val + 1 = k then spIn (Φ (if last = true then k else k - 1)) (Φ j2)
                else spIn (Φ j1) (Φ j2) := by
            refine Finset.prod_congr rfl fun e _ => ?_
            have hne_last : ¬ (e.castSucc.val + 1 = k + 1) := by simp; omega
            simp only [hne_last, ↓reduceIte]
            have hj1 := pathNP1Perm_castSucc_odd hk1 hk b₁ last e
            have hj2 : (pathNP2Perm (k + 1) b₂ e.castSucc).val =
                (pathNP2Perm k (boolCastEquiv (by omega : (k + 1 - 1) / 2 = (k - 1) / 2) b₂) e).val := by
              dsimp only [pathNP2Perm, Equiv.coe_fn_mk, boolCastEquiv]
              have hiff : (0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1) ↔
                  (0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k) := by simp; omega
              by_cases h1 : 0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k
              · have h2 := hiff.mpr h1
                have hbit : b₂ ⟨(e.castSucc.val - 1) / 2, by omega⟩ =
                    b₂ ⟨(e.val - 1) / 2, by omega⟩ :=
                  congrArg b₂ (Fin.ext (by simp only [Fin.val_castSucc]))
                simp only [h1.1, h1.2, h2.1, h2.2, and_self, ↓reduceDIte, hbit]
                by_cases hb : b₂ ⟨(e.val - 1) / 2, by omega⟩ = true
                · simp only [hb, ↓reduceIte, Fin.val_castSucc]
                · simp only [hb, Bool.false_eq_true, ↓reduceIte]; rfl
              · have h2 : ¬ (0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1) :=
                  fun hc => h1 (hiff.mp hc)
                simp only [h1, h2, ↓reduceDIte]; rfl
            rw [hj1, hj2]
            by_cases hel : e.val + 1 = k
            · simp only [hel, ↓reduceIte]
              have hfix1 : (pathNP1Perm k b₁ e).val = k - 1 := by
                dsimp only [pathNP1Perm, Equiv.coe_fn_mk]
                have hnot : ¬ (2 * (e.val / 2) + 1 < k) := by omega
                simp only [hnot, ↓reduceDIte]; omega
              cases last <;> simp [hfix1]
            · simp [hel]
          exact congrArg₂ (· * ·) hrest hlast)]
    have hsplit : (∑ b₁ : Fin ((k + 1) / 2) → Bool, ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
        ∏ e : Fin (k + 1),
          let j1 := (pathNP1Perm (k + 1) b₁ e).val
          let j2 := (pathNP2Perm (k + 1) b₂ e).val
          if e.val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2)) =
        ∑ p : (Fin (k / 2) → Bool) × Bool, ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁ := boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) p
            let j1 := (pathNP1Perm (k + 1) b₁ e).val
            let j2 := (pathNP2Perm (k + 1) b₂ e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2) :=
      (Fintype.sum_equiv (boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1))
        (fun p => ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁ := boolSnocCast (by omega : (k + 1) / 2 = k / 2 + 1) p
            let j1 := (pathNP1Perm (k + 1) b₁ e).val
            let j2 := (pathNP2Perm (k + 1) b₂ e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2))
        (fun b₁ => ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let j1 := (pathNP1Perm (k + 1) b₁ e).val
            let j2 := (pathNP2Perm (k + 1) b₂ e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2))
        (fun _ => rfl)).symm
    rw [hsplit, Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_bool, hbranch false, hbranch true]
    simp only [Bool.false_eq_true, ↓reduceIte, hk1]
    ring
  · have hk0 : k % 2 = 0 := by omega
    have hk2 : 2 ≤ k := by omega
    have hkmod : (k + 1) % 2 = 1 := by omega
    simp only [hk1, ↓reduceIte]
    unfold pathEndSum
    have hbranch : ∀ (last : Bool),
        (∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
            let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂' e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2)) =
        (∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k - 1) / 2) → Bool,
          ∏ e : Fin k,
            let j1 := (pathNP1Perm k b₁ e).val
            let j2 := (pathNP2Perm k b₂ e).val
            if e.val + 1 = k then spIn (Φ j1) (Φ (if last = true then k else k - 1))
            else spIn (Φ j1) (Φ j2)) *
          spIn x (Φ (if last = true then k - 1 else k)) := by
      intro last
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b₁ _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b₂ _ => ?_
      rw [Fin.prod_univ_castSucc]
      have hlast : (let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
          let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
          let j1 := (pathNP1Perm (k + 1) b₁' (Fin.last k)).val
          let j2 := (pathNP2Perm (k + 1) b₂' (Fin.last k)).val
          if (Fin.last k).val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2)) =
          spIn x (Φ (if last = true then k - 1 else k)) := by
        simp only [Fin.val_last, ↓reduceIte, hkmod, pathNP2Perm_last_even hk0 hk2 b₂ last]
      have hrest : (∏ e : Fin k,
          let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
          let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
          let j1 := (pathNP1Perm (k + 1) b₁' e.castSucc).val
          let j2 := (pathNP2Perm (k + 1) b₂' e.castSucc).val
          if e.castSucc.val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2)) =
          ∏ e : Fin k,
            let j1 := (pathNP1Perm k b₁ e).val
            let j2 := (pathNP2Perm k b₂ e).val
            if e.val + 1 = k then spIn (Φ j1) (Φ (if last = true then k else k - 1))
            else spIn (Φ j1) (Φ j2) := by
        refine Finset.prod_congr rfl fun e _ => ?_
        have hne_last : ¬ (e.castSucc.val + 1 = k + 1) := by simp; omega
        simp only [hne_last, ↓reduceIte]
        have hj1 : (pathNP1Perm (k + 1) (boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁) e.castSucc).val =
            (pathNP1Perm k b₁ e).val := by
          dsimp only [pathNP1Perm, Equiv.coe_fn_mk, boolCastEquiv]
          have hiff : 2 * (e.castSucc.val / 2) + 1 < k + 1 ↔ 2 * (e.val / 2) + 1 < k := by
            simp only [Fin.val_castSucc]; omega
          by_cases h1 : 2 * (e.val / 2) + 1 < k
          · have h2 := hiff.mpr h1
            have hbit : b₁ ⟨e.castSucc.val / 2, by omega⟩ = b₁ ⟨e.val / 2, by omega⟩ :=
              congrArg b₁ (Fin.ext (by simp only [Fin.val_castSucc]))
            simp only [h1, h2, ↓reduceDIte, hbit]
            by_cases hb : b₁ ⟨e.val / 2, by omega⟩ = true
            · simp only [hb, ↓reduceIte, Fin.val_castSucc]
            · simp only [hb, Bool.false_eq_true, ↓reduceIte]; rfl
          · have h2 : ¬ (2 * (e.castSucc.val / 2) + 1 < k + 1) := fun hc => h1 (hiff.mp hc)
            simp only [h1, h2, ↓reduceDIte]; rfl
        have hj2 : (pathNP2Perm (k + 1)
            (boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)) e.castSucc).val =
            if last = true ∧ e.val + 1 = k then k else (pathNP2Perm k b₂ e).val := by
          dsimp only [pathNP2Perm, Equiv.coe_fn_mk]
          by_cases hel : e.val + 1 = k
          · have hm_succ : 0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1 := by
              simp only [Fin.val_castSucc]; omega
            have hm_k : ¬ (0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k) := by omega
            have hb_eq : boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
                ⟨(e.castSucc.val - 1) / 2, by omega⟩ = last := by
              dsimp only [boolSnocCast, Equiv.coe_fn_mk]
              simp only [(by simp only [Fin.val_castSucc]; omega : ¬ (e.castSucc.val - 1) / 2 < (k - 1) / 2), ↓reduceDIte]
            simp only [hm_succ.1, hm_succ.2, and_self, hm_k, ↓reduceDIte, hb_eq]
            by_cases hlast : last = true
            · simp only [hlast, ↓reduceIte, hel, and_self]
              dsimp only [Fin.val_castSucc]; omega
            · simp only [hlast, Bool.false_eq_true, ↓reduceIte, false_and]; rfl
          · by_cases hm_k : 0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k
            · have hm_succ : 0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1 := by
                simp only [Fin.val_castSucc]; omega
              have hb_eq : boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
                  ⟨(e.castSucc.val - 1) / 2, by omega⟩ = b₂ ⟨(e.val - 1) / 2, by omega⟩ := by
                dsimp only [boolSnocCast, Equiv.coe_fn_mk]
                simp only [(by simp only [Fin.val_castSucc]; omega : (e.castSucc.val - 1) / 2 < (k - 1) / 2), ↓reduceDIte]
                exact congrArg b₂ (Fin.ext (by simp only [Fin.val_castSucc]))
              simp only [hm_succ.1, hm_succ.2, hm_k.1, hm_k.2, and_self, ↓reduceDIte, hb_eq, hel, and_false, ↓reduceIte]
              by_cases hb : b₂ ⟨(e.val - 1) / 2, by omega⟩ = true
              · simp only [hb, ↓reduceIte, Fin.val_castSucc]
              · simp only [hb, Bool.false_eq_true, ↓reduceIte]; rfl
            · have hm_succ : ¬ (0 < e.castSucc.val ∧ 2 * ((e.castSucc.val - 1) / 2) + 2 < k + 1) := by
                simp only [Fin.val_castSucc]; omega
              simp only [hm_succ, hm_k, ↓reduceDIte, hel, and_false, ↓reduceIte]; rfl
        rw [hj1, hj2]
        by_cases hel : e.val + 1 = k
        · simp only [hel, ↓reduceIte]
          have hfix2 : (pathNP2Perm k b₂ e).val = k - 1 := by
            dsimp only [pathNP2Perm, Equiv.coe_fn_mk]
            have hnot : ¬ (0 < e.val ∧ 2 * ((e.val - 1) / 2) + 2 < k) := by omega
            simp only [hnot, ↓reduceDIte]; omega
          cases last <;> simp [hfix2]
        · simp [hel]
      exact congrArg₂ (· * ·) hrest hlast
    have hsplit1 : (∑ b₁ : Fin ((k + 1) / 2) → Bool, ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
        ∏ e : Fin (k + 1),
          let j1 := (pathNP1Perm (k + 1) b₁ e).val
          let j2 := (pathNP2Perm (k + 1) b₂ e).val
          if e.val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2)) =
        ∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂ e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2) :=
      (Fintype.sum_equiv (boolCastEquiv (by omega : k / 2 = (k + 1) / 2))
        (fun b₁ => ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂ e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2))
        (fun b₁ => ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let j1 := (pathNP1Perm (k + 1) b₁ e).val
            let j2 := (pathNP2Perm (k + 1) b₂ e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2))
        (fun _ => rfl)).symm
    have hsplit2 : (∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k + 1 - 1) / 2) → Bool,
        ∏ e : Fin (k + 1),
          let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
          let j1 := (pathNP1Perm (k + 1) b₁' e).val
          let j2 := (pathNP2Perm (k + 1) b₂ e).val
          if e.val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2)) =
        ∑ b₁ : Fin (k / 2) → Bool, ∑ p : (Fin ((k - 1) / 2) → Bool) × Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
            let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) p
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂' e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2) := by
      refine Finset.sum_congr rfl fun b₁ _ => ?_
      exact (Fintype.sum_equiv (boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1))
        (fun p => ∏ e : Fin (k + 1),
          let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
          let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) p
          let j1 := (pathNP1Perm (k + 1) b₁' e).val
          let j2 := (pathNP2Perm (k + 1) b₂' e).val
          if e.val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2))
        (fun b₂ => ∏ e : Fin (k + 1),
          let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
          let j1 := (pathNP1Perm (k + 1) b₁' e).val
          let j2 := (pathNP2Perm (k + 1) b₂ e).val
          if e.val + 1 = k + 1 then
            if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
          else spIn (Φ j1) (Φ j2))
        (fun _ => rfl)).symm
    rw [hsplit1, hsplit2]
    have hcomm : (∑ b₁ : Fin (k / 2) → Bool, ∑ p : (Fin ((k - 1) / 2) → Bool) × Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
            let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) p
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂' e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2)) =
        ∑ last : Bool, ∑ b₁ : Fin (k / 2) → Bool, ∑ b₂ : Fin ((k - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
            let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂' e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2) := by
      trans ∑ b₁ : Fin (k / 2) → Bool, ∑ last : Bool, ∑ b₂ : Fin ((k - 1) / 2) → Bool,
          ∏ e : Fin (k + 1),
            let b₁' := boolCastEquiv (by omega : k / 2 = (k + 1) / 2) b₁
            let b₂' := boolSnocCast (by omega : (k + 1 - 1) / 2 = (k - 1) / 2 + 1) (b₂, last)
            let j1 := (pathNP1Perm (k + 1) b₁' e).val
            let j2 := (pathNP2Perm (k + 1) b₂' e).val
            if e.val + 1 = k + 1 then
              if (k + 1) % 2 = 1 then spIn x (Φ j2) else spIn (Φ j1) x
            else spIn (Φ j1) (Φ j2)
      · refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      · exact Finset.sum_comm
    rw [hcomm, Fintype.sum_bool, hbranch false, hbranch true]
    simp only [Bool.false_eq_true, ↓reduceIte, hk1]
    ring

/-- Iterative spinor-vector transfer recurrence `(a_k, w_k)` for path prefixes (`k ≥ 1`). -/
noncomputable def pathRecPair (Φ : ℕ → Fin 2 → ℂ) : ℕ → ℂ × (Fin 2 → ℂ)
  | 0 => (1, Φ 0)
  | 1 => (1, Φ 0)
  | k + 2 =>
      let k' := k + 1
      let p := pathRecPair Φ k'
      if k' % 2 = 1 then
        let d := spIn (Φ k') p.2
        (p.1 + d * spIn (Φ (k' - 1)) (Φ k'),
          fun j => starRingEnd ℂ p.1 * Φ k' j + starRingEnd ℂ d * Φ (k' - 1) j)
      else
        let d := spIn p.2 (Φ k')
        (p.1 + d * spIn (Φ k') (Φ (k' - 1)),
          fun j => p.1 * Φ k' j + d * Φ (k' - 1) j)

private lemma pathRecPair_succ_odd (Φ : ℕ → Fin 2 → ℂ) {k : ℕ} (h : (k + 1) % 2 = 1) :
    pathRecPair Φ (k + 2) =
      ((pathRecPair Φ (k + 1)).1 +
          spIn (Φ (k + 1)) (pathRecPair Φ (k + 1)).2 * spIn (Φ k) (Φ (k + 1)),
        fun j => starRingEnd ℂ (pathRecPair Φ (k + 1)).1 * Φ (k + 1) j +
          starRingEnd ℂ (spIn (Φ (k + 1)) (pathRecPair Φ (k + 1)).2) * Φ k j) := by
  simp only [pathRecPair, h, ↓reduceIte, Nat.add_sub_cancel]

private lemma pathRecPair_succ_even (Φ : ℕ → Fin 2 → ℂ) {k : ℕ} (h : ¬ (k + 1) % 2 = 1) :
    pathRecPair Φ (k + 2) =
      ((pathRecPair Φ (k + 1)).1 +
          spIn (pathRecPair Φ (k + 1)).2 (Φ (k + 1)) * spIn (Φ (k + 1)) (Φ k),
        fun j => (pathRecPair Φ (k + 1)).1 * Φ (k + 1) j +
          spIn (pathRecPair Φ (k + 1)).2 (Φ (k + 1)) * Φ k j) := by
  simp only [pathRecPair, h, ↓reduceIte, Nat.add_sub_cancel]

lemma spIn_conj_symm (u v : Fin 2 → ℂ) : spIn u v = starRingEnd ℂ (spIn v u) := by
  simp only [spIn, map_add, map_mul, Complex.conj_conj]
  ring

lemma spIn_jTilde_self (u : Fin 2 → ℂ) : spIn (jTilde u) u = 0 := by
  simp only [spIn, jTilde, Complex.conj_conj, map_neg]
  ring

/-- Exact equivalence between `pathEndSum`, `pathGramSum`, and `pathRecPair` for all `k ≥ 1`. -/
theorem pathEndSum_eq_rec (Φ : ℕ → Fin 2 → ℂ)
    (hunit : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = 1) :
    ∀ k : ℕ, 1 ≤ k →
      (k % 2 = 1 → spIn (Φ (k - 1)) (pathRecPair Φ k).2 = (pathRecPair Φ k).1 ∧
        ∀ x, pathEndSum k Φ x = spIn x (pathRecPair Φ k).2) ∧
      (k % 2 = 0 → spIn (Φ (k - 1)) (pathRecPair Φ k).2 = starRingEnd ℂ (pathRecPair Φ k).1 ∧
        ∀ x, pathEndSum k Φ x = spIn (pathRecPair Φ k).2 x)
  | 0, hk => absurd hk (by omega)
  | 1, _ => by
      refine ⟨fun _ => ⟨spIn_self_unit (hunit 0), fun x => ?_⟩, fun h0 => absurd h0 (by decide)⟩
      unfold pathEndSum pathRecPair
      have : Unique (Fin (1 / 2) → Bool) := ⟨⟨default⟩, fun f => funext fun j => absurd j.isLt (by norm_num)⟩
      have : Unique (Fin ((1 - 1) / 2) → Bool) := ⟨⟨default⟩, fun f => funext fun j => absurd j.isLt (by norm_num)⟩
      rw [Fintype.sum_unique, Fintype.sum_unique, Fin.prod_univ_one]
      simp
  | k + 2, _ => by
      let k' := k + 1
      have hk' : 1 ≤ k' := by omega
      have ih := pathEndSum_eq_rec Φ hunit k' hk'
      by_cases hk1 : (k + 1) % 2 = 1
      · refine ⟨fun h => absurd h (by omega), fun _ => ⟨?_, fun x => ?_⟩⟩
        · change spIn (Φ (k + 1)) (pathRecPair Φ (k + 2)).2 = starRingEnd ℂ (pathRecPair Φ (k + 2)).1
          rw [pathRecPair_succ_odd Φ hk1]
          simp only [spIn_add_smul_right, spIn_self_unit (hunit (k + 1)), mul_one, map_add,
            map_mul, ← spIn_conj_symm (Φ (k + 1)) (Φ k)]
        · rw [pathEndSum_succ k' hk' Φ x]
          have hkm : k' % 2 = 1 := hk1
          simp only [hkm, ↓reduceIte]
          have ihL := ih.1 hk1
          rw [ihL.2 (Φ (k' - 1)), ihL.2 (Φ k'), ihL.1]
          change _ = spIn (pathRecPair Φ (k + 2)).2 x
          rw [pathRecPair_succ_odd Φ hk1]
          simp only [spIn_add_smul_left, Complex.conj_conj]
          change (pathRecPair Φ (k + 1)).1 * spIn (Φ (k + 1)) x +
              spIn (Φ (k + 1)) (pathRecPair Φ (k + 1)).2 * spIn (Φ k) x = _
          ring
      · have hk0 : k' % 2 = 0 := by omega
        refine ⟨fun _ => ⟨?_, fun x => ?_⟩, fun h => absurd h (by omega)⟩
        · change spIn (Φ (k + 1)) (pathRecPair Φ (k + 2)).2 = (pathRecPair Φ (k + 2)).1
          rw [pathRecPair_succ_even Φ hk1]
          simp only [spIn_add_smul_right, spIn_self_unit (hunit (k + 1)), mul_one,
            spIn_conj_symm (Φ (k + 1)) (Φ k)]
        · rw [pathEndSum_succ k' hk' Φ x]
          have hkm : ¬ k' % 2 = 1 := hk1
          simp only [hkm, ↓reduceIte]
          have ihR := ih.2 hk0
          rw [ihR.2 (Φ (k' - 1)), ihR.2 (Φ k'), spIn_conj_symm (pathRecPair Φ k').2 (Φ (k' - 1)),
            ihR.1, Complex.conj_conj]
          change _ = spIn x (pathRecPair Φ (k + 2)).2
          rw [pathRecPair_succ_even Φ hk1]
          simp only [spIn_add_smul_right]
          change (pathRecPair Φ (k + 1)).1 * spIn x (Φ (k + 1)) +
              spIn (pathRecPair Φ (k + 1)).2 (Φ (k + 1)) * spIn x (Φ k) = _
          ring

lemma pathGramSum_eq_rec (Φ : ℕ → Fin 2 → ℂ)
    (hunit : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = 1) (m : ℕ) (hm : 1 ≤ m) :
    pathGramSum m Φ = (pathRecPair Φ m).1 := by
  rw [← pathEndSum_self m hm Φ]
  have hrec := pathEndSum_eq_rec Φ hunit m hm
  by_cases hm1 : m % 2 = 1
  · rw [(hrec.1 hm1).2 (Φ (m - 1)), (hrec.1 hm1).1]
  · have hm0 : m % 2 = 0 := by omega
    have hsp := (hrec.2 hm0).2 (Φ (m - 1))
    rw [hsp, spIn_conj_symm, (hrec.2 hm0).1, Complex.conj_conj]

private noncomputable def pathBeta (Φ : ℕ → Fin 2 → ℂ) (k : ℕ) : ℂ :=
  if k % 2 = 1 then spIn (jTilde (Φ (k - 1))) (pathRecPair Φ k).2
  else starRingEnd ℂ (spIn (jTilde (Φ (k - 1))) (pathRecPair Φ k).2)

/-- For all `k ≥ 1`, `‖(pathRecPair Φ k).1‖^2 - ‖pathBeta Φ k‖^2 ≥ 1`. -/
theorem pathRecPair_hyperbolic_ge_one (Φ : ℕ → Fin 2 → ℂ)
    (hunit : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = 1) :
    ∀ k : ℕ, 1 ≤ k → 1 ≤ ‖(pathRecPair Φ k).1‖ ^ 2 - ‖pathBeta Φ k‖ ^ 2
  | 0, hk => absurd hk (by omega)
  | 1, _ => by
      have hβ : pathBeta Φ 1 = 0 := by
        simp only [pathBeta, pathRecPair, show 1 % 2 = 1 from rfl, ↓reduceIte, Nat.sub_self]
        exact spIn_jTilde_self (Φ 0)
      rw [hβ, norm_zero, pathRecPair]
      norm_num
  | k + 2, _ => by
      let k' := k + 1
      have hk' : 1 ≤ k' := by omega
      have ih := pathRecPair_hyperbolic_ge_one Φ hunit k' hk'
      have hrec := pathEndSum_eq_rec Φ hunit k' hk'
      have hw_exp : (pathRecPair Φ k').2 = fun j =>
          spIn (Φ (k' - 1)) (pathRecPair Φ k').2 * Φ (k' - 1) j +
          spIn (jTilde (Φ (k' - 1))) (pathRecPair Φ k').2 * jTilde (Φ (k' - 1)) j :=
        spIn_basis_expand (hunit (k' - 1)) (pathRecPair Φ k').2
      by_cases hk1 : k' % 2 = 1
      · have hmod0 : ¬ (k + 2) % 2 = 1 := by omega
        have ha_eq : spIn (Φ (k' - 1)) (pathRecPair Φ k').2 = (pathRecPair Φ k').1 :=
          (hrec.1 hk1).1
        have hβ_eq : spIn (jTilde (Φ (k' - 1))) (pathRecPair Φ k').2 = pathBeta Φ k' := by
          simp [pathBeta, hk1]
        let U := spIn (Φ k') (Φ (k' - 1))
        let V := spIn (Φ k') (jTilde (Φ (k' - 1)))
        have hUV : ‖U‖ ^ 2 + ‖V‖ ^ 2 = 1 := by
          have ho := spIn_ortho_basis (hunit (k' - 1)) (hunit k')
          have hU' : ‖U‖ = ‖spIn (Φ (k' - 1)) (Φ k')‖ := by
            rw [spIn_conj_symm, Complex.norm_conj]
          have hV' : ‖V‖ = ‖spIn (jTilde (Φ (k' - 1))) (Φ k')‖ := by
            rw [spIn_conj_symm, Complex.norm_conj]
          rw [hU', hV']
          exact ho
        have hd_eq : spIn (Φ k') (pathRecPair Φ k').2 = U * (pathRecPair Φ k').1 + V * pathBeta Φ k' := by
          conv_lhs => rw [hw_exp, ha_eq, hβ_eq]
          rw [spIn_add_smul_right]
          ring
        have ha_nx : (pathRecPair Φ (k + 2)).1 =
            (pathRecPair Φ k').1 + starRingEnd ℂ U * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k') := by
          rw [pathRecPair_succ_odd Φ hk1]
          change (pathRecPair Φ k').1 + spIn (Φ k') (pathRecPair Φ k').2 * spIn (Φ (k' - 1)) (Φ k') = _
          rw [hd_eq, spIn_conj_symm (Φ (k' - 1)) (Φ k')]
          ring
        have hβ_nx_norm : ‖pathBeta Φ (k + 2)‖ ^ 2 =
            ‖-V * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k')‖ ^ 2 := by
          have hbe : pathBeta Φ (k + 2) =
              starRingEnd ℂ (spIn (jTilde (Φ k')) (pathRecPair Φ (k + 2)).2) := by
            dsimp only [pathBeta]
            simp only [hmod0, ↓reduceIte]
            rfl
          have hsp : spIn (jTilde (Φ k')) (pathRecPair Φ (k + 2)).2 =
              starRingEnd ℂ (spIn (Φ k') (pathRecPair Φ k').2) * spIn (jTilde (Φ k')) (Φ (k' - 1)) := by
            rw [pathRecPair_succ_odd Φ hk1]
            change spIn (jTilde (Φ (k + 1))) _ = _
            simp only [spIn_add_smul_right, spIn_jTilde_self (Φ (k + 1)), mul_zero, zero_add]
            rfl
          rw [hbe, hsp, map_mul, Complex.conj_conj, hd_eq, spIn_flip_jTilde_right (hunit (k' - 1)),
            map_neg]
          simp only [norm_mul, norm_neg, Complex.norm_conj, V]
          rw [show ‖spIn (jTilde (Φ (k' - 1))) (Φ k')‖ = ‖spIn (Φ k') (jTilde (Φ (k' - 1)))‖ by
            rw [spIn_conj_symm, Complex.norm_conj]]
          ring
        have hid := hyperbolic_step_id (pathRecPair Φ k').1 (pathBeta Φ k') U V hUV
        dsimp only at hid
        rw [← ha_nx, ← hβ_nx_norm] at hid
        have hnn : 0 ≤ ‖U‖ ^ 2 * (3 * ‖U * (pathRecPair Φ k').1 + V * pathBeta Φ k'‖ ^ 2 +
            ‖-starRingEnd ℂ V * (pathRecPair Φ k').1 + starRingEnd ℂ U * pathBeta Φ k'‖ ^ 2) := by
          positivity
        linarith
      · have hk0 : k' % 2 = 0 := by omega
        have hmod1 : (k + 2) % 2 = 1 := by omega
        have ha_eq : spIn (Φ (k' - 1)) (pathRecPair Φ k').2 = starRingEnd ℂ (pathRecPair Φ k').1 :=
          (hrec.2 hk0).1
        have hβ_eq : spIn (jTilde (Φ (k' - 1))) (pathRecPair Φ k').2 = starRingEnd ℂ (pathBeta Φ k') := by
          simp [pathBeta, hk1]
        let U := spIn (Φ (k' - 1)) (Φ k')
        let V := spIn (jTilde (Φ (k' - 1))) (Φ k')
        have hUV : ‖U‖ ^ 2 + ‖V‖ ^ 2 = 1 := spIn_ortho_basis (hunit (k' - 1)) (hunit k')
        have hd_eq : spIn (pathRecPair Φ k').2 (Φ k') =
            U * (pathRecPair Φ k').1 + V * pathBeta Φ k' := by
          conv_lhs => rw [hw_exp, ha_eq, hβ_eq]
          rw [spIn_add_smul_left, Complex.conj_conj, Complex.conj_conj]
          ring
        have ha_nx : (pathRecPair Φ (k + 2)).1 =
            (pathRecPair Φ k').1 + starRingEnd ℂ U * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k') := by
          rw [pathRecPair_succ_even Φ hk1]
          change (pathRecPair Φ k').1 + spIn (pathRecPair Φ k').2 (Φ k') * spIn (Φ k') (Φ (k' - 1)) = _
          rw [hd_eq, spIn_conj_symm (Φ k') (Φ (k' - 1))]
          ring
        have hβ_nx_norm : ‖pathBeta Φ (k + 2)‖ ^ 2 =
            ‖-V * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k')‖ ^ 2 := by
          have hbe : pathBeta Φ (k + 2) = spIn (jTilde (Φ k')) (pathRecPair Φ (k + 2)).2 := by
            dsimp only [pathBeta]
            simp only [hmod1, ↓reduceIte]
            rfl
          have hsp : spIn (jTilde (Φ k')) (pathRecPair Φ (k + 2)).2 =
              spIn (pathRecPair Φ k').2 (Φ k') * spIn (jTilde (Φ k')) (Φ (k' - 1)) := by
            rw [pathRecPair_succ_even Φ hk1]
            change spIn (jTilde (Φ (k + 1))) _ = _
            simp only [spIn_add_smul_right, spIn_jTilde_self (Φ (k + 1)), mul_zero, zero_add]
            rfl
          rw [hbe, hsp, hd_eq, spIn_flip_jTilde_right (hunit (k' - 1))]
          simp only [norm_mul, norm_neg, V]
          ring
        have hid := hyperbolic_step_id (pathRecPair Φ k').1 (pathBeta Φ k') U V hUV
        dsimp only at hid
        rw [← ha_nx, ← hβ_nx_norm] at hid
        have hnn : 0 ≤ ‖U‖ ^ 2 * (3 * ‖U * (pathRecPair Φ k').1 + V * pathBeta Φ k'‖ ^ 2 +
            ‖-starRingEnd ℂ V * (pathRecPair Φ k').1 + starRingEnd ℂ U * pathBeta Φ k'‖ ^ 2) := by
          positivity
        linarith

theorem pathGramSum_norm_ge_one (Φ : ℕ → Fin 2 → ℂ)
    (hunit : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = 1) (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ ‖pathGramSum m Φ‖ := by
  rw [pathGramSum_eq_rec Φ hunit m hm]
  have hhyp := pathRecPair_hyperbolic_ge_one Φ hunit m hm
  have hsq : 1 ≤ ‖(pathRecPair Φ m).1‖ ^ 2 := by linarith [sq_nonneg ‖pathBeta Φ m‖]
  nlinarith [norm_nonneg (pathRecPair Φ m).1]

end SpinorPathRecurrence

/-! ## Part 3: Unconditional Path Conjecture B (`‖A_{LG_n}(x)‖ ≥ 1`) and A (`A_{LG_n}(x) ≠ 0`) -/

section PathConjecturesBA

private lemma malkounAmplitude_pathGraphN_small (n : ℕ) (hn : n ≤ 1) (x : ConfigSpace (pathGraphN n)) :
    malkounAmplitude (pathGraphN n) x = 1 := by
  have hempty : IsEmpty (BipEdge (pathGraphN n) partEvenN) := ⟨fun e => by
    have hadj := e.2.1
    have hu := e.1.1.isLt
    have hv := e.1.2.isLt
    rcases hadj with h | h <;> omega⟩
  rw [malkounAmplitude_bipartite_eq_conj_gram (pathGraphN n) partEvenN (pathGraphN_isBipartite n) x]
  have hp1 : Unique (bipP1 (pathGraphN n) partEvenN) := by
    refine ⟨⟨1⟩, fun a => Subtype.ext (Equiv.ext fun e => False.elim (hempty.false e))⟩
  have hp2 : Unique (bipP2 (pathGraphN n) partEvenN) := by
    refine ⟨⟨1⟩, fun a => Subtype.ext (Equiv.ext fun e => False.elim (hempty.false e))⟩
  simp

private lemma pathGraphN_gram_eq_pathGramSum (m : ℕ) (x : ConfigSpace (pathGraphN (m + 1)))
    (Φe : BipEdge (pathGraphN (m + 1)) partEvenN → Fin 2 → ℂ)
    (hnorm : ∀ e, ‖Φe e 0‖ ^ 2 + ‖Φe e 1‖ ^ 2 = 1)
    (hmul : ∀ e, (pauliDot (unitDir (x.1 e.1.1) (x.1 e.1.2))).mulVec (Φe e) = Φe e)
    (d : Fin 2 → ℂ) :
    let Φ : ℕ → Fin 2 → ℂ := fun k =>
      if h : k < m then Φe (pathNEdges m ⟨k, h⟩) else d
    malkounAmplitude (pathGraphN (m + 1)) x = starRingEnd ℂ (pathGramSum m Φ) := by
  intro Φ
  have hr1 : ∀ _ : BipEdge (pathGraphN (m + 1)) partEvenN, (0 : ℝ) < 1 := fun _ => by norm_num
  rw [malkounAmplitude_bipartite_unnorm (pathGraphN (m + 1)) partEvenN (pathGraphN_isBipartite _) x
      Φe (fun _ : BipEdge (pathGraphN (m + 1)) partEvenN => (1 : ℝ)) hr1 hnorm hmul]
  simp only [Finset.prod_const_one, Complex.ofReal_one, div_one]
  congr 1
  rw [← Fintype.sum_equiv (pathNP1Equiv m) _ _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [← Fintype.sum_equiv (pathNP2Equiv m) _ _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [← Fintype.prod_equiv (pathNEdgeEquiv m) _ _ (fun _ => rfl)]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hs1 : (pathNP1Equiv m b₁).1 (pathNEdgeEquiv m e) =
      pathNEdges m (pathNP1Perm m b₁ e) := by
    simp only [pathNP1Equiv, Equiv.coe_fn_mk, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  have hs2 : (pathNP2Equiv m b₂).1 (pathNEdgeEquiv m e) =
      pathNEdges m (pathNP2Perm m b₂ e) := by
    simp only [pathNP2Equiv, Equiv.coe_fn_mk, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  rw [hs1, hs2]
  simp only [spIn, Φ, (pathNP1Perm m b₁ e).isLt, (pathNP2Perm m b₂ e).isLt, ↓reduceDIte]

private lemma pathSpinorExt_unit (m : ℕ) (Φe : BipEdge (pathGraphN (m + 1)) partEvenN → Fin 2 → ℂ)
    (hnorm : ∀ e, ‖Φe e 0‖ ^ 2 + ‖Φe e 1‖ ^ 2 = 1)
    {d : Fin 2 → ℂ} (hd : ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 = 1) :
    ∀ k : ℕ, ‖(if h : k < m then Φe (pathNEdges m ⟨k, h⟩) else d) 0‖ ^ 2 +
      ‖(if h : k < m then Φe (pathNEdges m ⟨k, h⟩) else d) 1‖ ^ 2 = 1 := by
  intro k
  by_cases h : k < m
  · simp only [h, ↓reduceDIte]; exact hnorm _
  · simp only [h, ↓reduceDIte]; exact hd

/-- **Unconditional Path Conjecture B (All $n \in \mathbb{N}$):**
For **every** linear path $LG_n$ and **every** 3D configuration `x : ConfigSpace (pathGraphN n)`,
$\|\mathcal{A}_{LG_n}(\mathbf{x})\| \ge 1$. -/
theorem malkounAmplitude_pathGraphN_norm_ge_one (n : ℕ) (x : ConfigSpace (pathGraphN n)) :
    1 ≤ ‖malkounAmplitude (pathGraphN n) x‖ := by
  rcases le_or_gt n 1 with hn1 | hn2
  · rw [malkounAmplitude_pathGraphN_small n hn1 x, norm_one]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hm : 1 ≤ m := by omega
    let Φe := bipEdgeSpinor x (G := pathGraphN (m + 1)) (part := partEvenN)
    have hnorm : ∀ e, ‖Φe e 0‖ ^ 2 + ‖Φe e 1‖ ^ 2 = 1 := fun e =>
      (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 e.1.1 e.1.2 e.2.1))).1
    have hmul : ∀ e, (pauliDot (unitDir (x.1 e.1.1) (x.1 e.1.2))).mulVec (Φe e) = Φe e := fun e =>
      (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 e.1.1 e.1.2 e.2.1))).2
    let d : Fin 2 → ℂ := ![1, 0]
    have hd : ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 = 1 := by simp [d]
    let Φ : ℕ → Fin 2 → ℂ := fun k => if h : k < m then Φe (pathNEdges m ⟨k, h⟩) else d
    rw [pathGraphN_gram_eq_pathGramSum m x Φe hnorm hmul d, Complex.norm_conj]
    exact pathGramSum_norm_ge_one Φ (pathSpinorExt_unit m Φe hnorm hd) m hm

/-- **Unconditional Path Conjecture A (All $n \in \mathbb{N}$):**
For **every** linear path $LG_n$ and **every** 3D configuration `x : ConfigSpace (pathGraphN n)`,
$\mathcal{A}_{LG_n}(\mathbf{x}) \neq 0$. -/
theorem malkounAmplitude_pathGraphN_ne_zero (n : ℕ) (x : ConfigSpace (pathGraphN n)) :
    malkounAmplitude (pathGraphN n) x ≠ 0 := by
  intro h0
  have hn := malkounAmplitude_pathGraphN_norm_ge_one n x
  rw [h0, norm_zero] at hn
  linarith

end PathConjecturesBA

/-! ## Part 4: Unconditional Planar Path Conjecture C (`Re (A_{LG_n}(x)) ≥ 1` for Planar Configs) -/

section PlanarPathConjectureC

private noncomputable def cayleyPlanarHalf (v : Fin 3 → ℝ) : Fin 2 → ℝ :=
  if -1 < v 0 then
    ![Real.sqrt ((1 + v 0) / 2), (if 0 ≤ v 1 then 1 else -1) * Real.sqrt ((1 - v 0) / 2)]
  else ![0, 1]

private lemma cayleyPlanarHalf_props {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) (hz : v 2 = 0) :
    let r := cayleyPlanarHalf v
    r 0 ^ 2 + r 1 ^ 2 = 1 ∧ r 0 ^ 2 - r 1 ^ 2 = v 0 ∧ 2 * r 0 * r 1 = v 1 := by
  have hv0_ge : -1 ≤ v 0 := by nlinarith [sq_nonneg (v 1), hz, sq_nonneg (v 0 + 1)]
  have hv0_le : v 0 ≤ 1 := by nlinarith [sq_nonneg (v 1), hz, sq_nonneg (v 0 - 1)]
  dsimp only [cayleyPlanarHalf]
  by_cases h0 : -1 < v 0
  · simp only [h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hs1 : Real.sqrt ((1 + v 0) / 2) ^ 2 = (1 + v 0) / 2 := Real.sq_sqrt (by linarith)
    have hs2 : Real.sqrt ((1 - v 0) / 2) ^ 2 = (1 - v 0) / 2 := Real.sq_sqrt (by linarith)
    have hsgn : (if 0 ≤ v 1 then (1 : ℝ) else -1) ^ 2 = 1 := by split_ifs <;> norm_num
    have hmul_sq : (2 * Real.sqrt ((1 + v 0) / 2) *
        ((if 0 ≤ v 1 then 1 else -1) * Real.sqrt ((1 - v 0) / 2))) ^ 2 = v 1 ^ 2 := by
      calc _ = 4 * Real.sqrt ((1 + v 0) / 2) ^ 2 * Real.sqrt ((1 - v 0) / 2) ^ 2 *
              (if 0 ≤ v 1 then (1 : ℝ) else -1) ^ 2 := by ring
        _ = 4 * ((1 + v 0) / 2) * ((1 - v 0) / 2) * 1 := by rw [hs1, hs2, hsgn]
        _ = 1 - v 0 ^ 2 := by ring
        _ = v 1 ^ 2 := by nlinarith [hv, hz]
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_pow, hs1, hs2, hsgn]; ring
    · rw [mul_pow, hs1, hs2, hsgn]; ring
    · have ha : 0 ≤ Real.sqrt ((1 + v 0) / 2) := Real.sqrt_nonneg _
      have hb : 0 ≤ Real.sqrt ((1 - v 0) / 2) := Real.sqrt_nonneg _
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hmul_sq with hpos | hneg
      · exact hpos
      · by_cases hv1 : 0 ≤ v 1
        · simp only [hv1, ↓reduceIte, one_mul] at hneg ⊢
          have hnn : 0 ≤ 2 * Real.sqrt ((1 + v 0) / 2) * Real.sqrt ((1 - v 0) / 2) := by positivity
          linarith
        · push Not at hv1
          simp only [not_le.mpr hv1, ↓reduceIte, neg_mul, one_mul] at hneg ⊢
          have hnp : 2 * Real.sqrt ((1 + v 0) / 2) * (-Real.sqrt ((1 - v 0) / 2)) ≤ 0 := by nlinarith
          linarith
  · have hv0 : v 0 = -1 := by linarith
    have hv1 : v 1 = 0 := by nlinarith [hv, hz, hv0]
    rw [hv0, hv1]
    norm_num

private noncomputable def cayleySpinor (r : Fin 2 → ℝ) : Fin 2 → ℂ :=
  ![((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ),
    ((r 0 : ℂ) + Complex.I * (r 1 : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ)]

private lemma cayley_comp_norm_sq (a b : ℝ) :
    ‖((a : ℂ) + Complex.I * (b : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = (a ^ 2 + b ^ 2) / 2 := by
  have hs2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs2_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma cayleySpinor_ok {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) (hz : v 2 = 0) :
    let ψ := cayleySpinor (cayleyPlanarHalf v)
    ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1 ∧ (pauliDot v).mulVec ψ = ψ := by
  obtain ⟨hsum, hdx, hdy⟩ := cayleyPlanarHalf_props hv hz
  set r := cayleyPlanarHalf v
  have hs2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2C : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs2_pos.ne'
  refine ⟨?_, ?_⟩
  · have hns0 : ‖cayleySpinor r 0‖ ^ 2 = (r 0 ^ 2 + r 1 ^ 2) / 2 := by
      have h0eq : cayleySpinor r 0 =
          (((r 0 : ℝ) : ℂ) + Complex.I * ((-r 1 : ℝ) : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ) := by
        simp only [cayleySpinor, Matrix.cons_val_zero, Complex.ofReal_neg]; ring
      rw [h0eq, cayley_comp_norm_sq (r 0) (-r 1), neg_sq]
    have hns1 : ‖cayleySpinor r 1‖ ^ 2 = (r 0 ^ 2 + r 1 ^ 2) / 2 := by
      have h1eq : cayleySpinor r 1 =
          (((r 0 : ℝ) : ℂ) + Complex.I * ((r 1 : ℝ) : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ) := by
        simp only [cayleySpinor, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h1eq, cayley_comp_norm_sq (r 0) (r 1)]
    rw [hns0, hns1, hsum]; norm_num
  · have hv_sub : (v 0 : ℂ) - Complex.I * (v 1 : ℂ) = ((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) ^ 2 := by
      rw [← hdx, ← hdy]
      push_cast
      rw [sub_sq]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hv_add : (v 0 : ℂ) + Complex.I * (v 1 : ℂ) = ((r 0 : ℂ) + Complex.I * (r 1 : ℂ)) ^ 2 := by
      rw [← hdx, ← hdy]
      push_cast
      rw [add_sq]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hr_unit : ((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) * ((r 0 : ℂ) + Complex.I * (r 1 : ℂ)) = 1 := by
      calc ((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) * ((r 0 : ℂ) + Complex.I * (r 1 : ℂ))
          = ((r 0 : ℂ) ^ 2 + (r 1 : ℂ) ^ 2) := by
            rw [sub_mul, mul_add, mul_add]; ring_nf; rw [Complex.I_sq]; ring
        _ = ((r 0 ^ 2 + r 1 ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        _ = 1 := by rw [hsum, Complex.ofReal_one]
    ext k
    rcases fin2_eq' k with rfl | rfl
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, cayleySpinor,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hz, Complex.ofReal_zero,
        zero_mul, zero_add]
      rw [hv_sub]
      calc (((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) ^ 2) *
            (((r 0 : ℂ) + Complex.I * (r 1 : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ))
          = ((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) *
              (((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) * ((r 0 : ℂ) + Complex.I * (r 1 : ℂ))) /
              ((Real.sqrt 2 : ℝ) : ℂ) := by ring
        _ = ((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ) := by
            rw [hr_unit, mul_one]
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, cayleySpinor,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hz, Complex.ofReal_zero,
        neg_zero, zero_mul, add_zero]
      rw [hv_add]
      calc (((r 0 : ℂ) + Complex.I * (r 1 : ℂ)) ^ 2) *
            (((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ))
          = ((r 0 : ℂ) + Complex.I * (r 1 : ℂ)) *
              (((r 0 : ℂ) - Complex.I * (r 1 : ℂ)) * ((r 0 : ℂ) + Complex.I * (r 1 : ℂ))) /
              ((Real.sqrt 2 : ℝ) : ℂ) := by ring
        _ = ((r 0 : ℂ) + Complex.I * (r 1 : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ) := by
            rw [hr_unit, mul_one]

private lemma cayleySpinor_spIn_im_zero (r₁ r₂ : Fin 2 → ℝ) :
    (spIn (cayleySpinor r₁) (cayleySpinor r₂)).im = 0 := by
  have hs2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [spIn, cayleySpinor, Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_sub,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.div_ofReal_im, Complex.div_ofReal_re,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp [hs2_pos.ne']
  ring

private lemma pathGramSum_im_zero_of_spIn_real (Φ : ℕ → Fin 2 → ℂ)
    (hreal : ∀ i j, (spIn (Φ i) (Φ j)).im = 0) (k : ℕ) :
    (pathGramSum k Φ).im = 0 := by
  unfold pathGramSum
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun b₁ _ => ?_
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun b₂ _ => ?_
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
      rw [Finset.prod_insert he, Complex.mul_im, ih,
        hreal (pathNP1Perm k b₁ e).val (pathNP2Perm k b₂ e).val]
      ring

private lemma pathRecPair_planar_pos (Φ : ℕ → Fin 2 → ℂ)
    (hunit : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = 1)
    (hreal : ∀ i j, (spIn (Φ i) (Φ j)).im = 0) :
    ∀ k : ℕ, 1 ≤ k → 0 < (pathRecPair Φ k).1.re
  | 0, hk => absurd hk (by omega)
  | 1, _ => by simp [pathRecPair]
  | k + 2, _ => by
      let k' := k + 1
      have hk' : 1 ≤ k' := by omega
      have ha_pos := pathRecPair_planar_pos Φ hunit hreal k' hk'
      have haim : (pathRecPair Φ k').1.im = 0 := by
        rw [← pathGramSum_eq_rec Φ hunit k' hk']
        exact pathGramSum_im_zero_of_spIn_real Φ hreal k'
      have hhyp := pathRecPair_hyperbolic_ge_one Φ hunit k' hk'
      have hrec := pathEndSum_eq_rec Φ hunit k' hk'
      have hw_exp : (pathRecPair Φ k').2 = fun j =>
          spIn (Φ (k' - 1)) (pathRecPair Φ k').2 * Φ (k' - 1) j +
          spIn (jTilde (Φ (k' - 1))) (pathRecPair Φ k').2 * jTilde (Φ (k' - 1)) j :=
        spIn_basis_expand (hunit (k' - 1)) (pathRecPair Φ k').2
      have ha_norm : ‖(pathRecPair Φ k').1‖ = (pathRecPair Φ k').1.re := by
        rw [Complex.norm_def, Complex.normSq_apply, haim, mul_zero, add_zero,
          ← sq, Real.sqrt_sq ha_pos.le]
      have hβ_le : ‖pathBeta Φ k'‖ ≤ (pathRecPair Φ k').1.re := by
        have h1 : ‖pathBeta Φ k'‖ ^ 2 ≤ (pathRecPair Φ k').1.re ^ 2 := by
          rw [← ha_norm]; linarith
        nlinarith [norm_nonneg (pathBeta Φ k'), ha_pos]
      have step_re : ∀ U V : ℂ, U.im = 0 → ‖U‖ ^ 2 + ‖V‖ ^ 2 = 1 →
          0 < ((pathRecPair Φ k').1 + starRingEnd ℂ U * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k')).re := by
        intro U V hUim hUV
        have hUc : U = ((U.re : ℝ) : ℂ) := Complex.ext rfl hUim
        have hac : (pathRecPair Φ k').1 = (((pathRecPair Φ k').1.re : ℝ) : ℂ) :=
          Complex.ext rfl haim
        have hrew : ((pathRecPair Φ k').1 + starRingEnd ℂ U * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k')).re =
            (1 + U.re ^ 2) * (pathRecPair Φ k').1.re + U.re * (V * pathBeta Φ k').re := by
          conv_lhs => rw [hUc, hac]
          simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero]
          ring
        have hV_bd : |(V * pathBeta Φ k').re| ≤ ‖V‖ * (pathRecPair Φ k').1.re := by
          calc |(V * pathBeta Φ k').re| ≤ ‖V * pathBeta Φ k'‖ := Complex.abs_re_le_norm _
            _ = ‖V‖ * ‖pathBeta Φ k'‖ := norm_mul _ _
            _ ≤ ‖V‖ * (pathRecPair Φ k').1.re := mul_le_mul_of_nonneg_left hβ_le (norm_nonneg V)
        have hUV_re : U.re ^ 2 + ‖V‖ ^ 2 = 1 := by
          rw [hUc, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hUV; exact hUV
        have hcross : |U.re * (V * pathBeta Φ k').re| ≤ (1 / 2 : ℝ) * (pathRecPair Φ k').1.re := by
          calc |U.re * (V * pathBeta Φ k').re|
              = |U.re| * |(V * pathBeta Φ k').re| := abs_mul _ _
            _ ≤ |U.re| * (‖V‖ * (pathRecPair Φ k').1.re) :=
                mul_le_mul_of_nonneg_left hV_bd (abs_nonneg U.re)
            _ = (|U.re| * ‖V‖) * (pathRecPair Φ k').1.re := by ring
            _ ≤ ((U.re ^ 2 + ‖V‖ ^ 2) / 2) * (pathRecPair Φ k').1.re := by
                refine mul_le_mul_of_nonneg_right ?_ ha_pos.le
                nlinarith [sq_nonneg (|U.re| - ‖V‖), sq_abs U.re]
            _ = (1 / 2 : ℝ) * (pathRecPair Φ k').1.re := by rw [hUV_re]
        rw [hrew]
        linarith [(neg_le_abs (U.re * (V * pathBeta Φ k').re)).trans hcross,
          mul_nonneg (sq_nonneg U.re) ha_pos.le]
      by_cases hk1 : k' % 2 = 1
      · have ha_eq : spIn (Φ (k' - 1)) (pathRecPair Φ k').2 = (pathRecPair Φ k').1 := (hrec.1 hk1).1
        have hβ_eq : spIn (jTilde (Φ (k' - 1))) (pathRecPair Φ k').2 = pathBeta Φ k' := by
          simp [pathBeta, hk1]
        let U := spIn (Φ k') (Φ (k' - 1))
        let V := spIn (Φ k') (jTilde (Φ (k' - 1)))
        have hUV : ‖U‖ ^ 2 + ‖V‖ ^ 2 = 1 := by
          have ho := spIn_ortho_basis (hunit (k' - 1)) (hunit k')
          rw [show ‖U‖ = ‖spIn (Φ (k' - 1)) (Φ k')‖ by rw [spIn_conj_symm, Complex.norm_conj],
              show ‖V‖ = ‖spIn (jTilde (Φ (k' - 1))) (Φ k')‖ by rw [spIn_conj_symm, Complex.norm_conj]]
          exact ho
        have hd_eq : spIn (Φ k') (pathRecPair Φ k').2 = U * (pathRecPair Φ k').1 + V * pathBeta Φ k' := by
          conv_lhs => rw [hw_exp, ha_eq, hβ_eq]
          rw [spIn_add_smul_right]; ring
        have ha_nx : (pathRecPair Φ (k + 2)).1 =
            (pathRecPair Φ k').1 + starRingEnd ℂ U * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k') := by
          rw [pathRecPair_succ_odd Φ hk1]
          change (pathRecPair Φ k').1 + spIn (Φ k') (pathRecPair Φ k').2 * spIn (Φ (k' - 1)) (Φ k') = _
          rw [hd_eq, spIn_conj_symm (Φ (k' - 1)) (Φ k')]
          ring
        rw [ha_nx]
        exact step_re U V (hreal k' (k' - 1)) hUV
      · have hk0 : k' % 2 = 0 := by omega
        have ha_eq : spIn (Φ (k' - 1)) (pathRecPair Φ k').2 = starRingEnd ℂ (pathRecPair Φ k').1 :=
          (hrec.2 hk0).1
        have hβ_eq : spIn (jTilde (Φ (k' - 1))) (pathRecPair Φ k').2 = starRingEnd ℂ (pathBeta Φ k') := by
          simp [pathBeta, hk1]
        let U := spIn (Φ (k' - 1)) (Φ k')
        let V := spIn (jTilde (Φ (k' - 1))) (Φ k')
        have hUV : ‖U‖ ^ 2 + ‖V‖ ^ 2 = 1 := spIn_ortho_basis (hunit (k' - 1)) (hunit k')
        have hd_eq : spIn (pathRecPair Φ k').2 (Φ k') = U * (pathRecPair Φ k').1 + V * pathBeta Φ k' := by
          conv_lhs => rw [hw_exp, ha_eq, hβ_eq]
          rw [spIn_add_smul_left, Complex.conj_conj, Complex.conj_conj]; ring
        have ha_nx : (pathRecPair Φ (k + 2)).1 =
            (pathRecPair Φ k').1 + starRingEnd ℂ U * (U * (pathRecPair Φ k').1 + V * pathBeta Φ k') := by
          rw [pathRecPair_succ_even Φ hk1]
          change (pathRecPair Φ k').1 + spIn (pathRecPair Φ k').2 (Φ k') * spIn (Φ k') (Φ (k' - 1)) = _
          rw [hd_eq, spIn_conj_symm (Φ k') (Φ (k' - 1))]
          ring
        rw [ha_nx]
        exact step_re U V (hreal (k' - 1) k') hUV

/-- **Unconditional Planar Path Conjecture C (All $n \in \mathbb{N}$):**
For **every** linear path $LG_n$ and **every** planar non-collision configuration `x` (`z_u = 0`),
$\operatorname{Re}(\mathcal{A}_{LG_n}(\mathbf{x})) \ge 1$. -/
theorem malkounAmplitude_pathGraphN_planar_re_ge_one (n : ℕ) (x : ConfigSpace (pathGraphN n))
    (hplanar : ∀ u, x.1 u 2 = 0) :
    1 ≤ (malkounAmplitude (pathGraphN n) x).re := by
  rcases le_or_gt n 1 with hn1 | hn2
  · rw [malkounAmplitude_pathGraphN_small n hn1 x, Complex.one_re]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hm : 1 ≤ m := by omega
    let eDir : BipEdge (pathGraphN (m + 1)) partEvenN → Fin 3 → ℝ :=
      fun e => unitDir (x.1 e.1.1) (x.1 e.1.2)
    have he_z : ∀ e, eDir e 2 = 0 := fun e => by
      simp only [eDir, unitDir, hplanar e.1.1, hplanar e.1.2, sub_self, zero_div]
    let Φe : BipEdge (pathGraphN (m + 1)) partEvenN → Fin 2 → ℂ :=
      fun e => cayleySpinor (cayleyPlanarHalf (eDir e))
    have hnorm : ∀ e, ‖Φe e 0‖ ^ 2 + ‖Φe e 1‖ ^ 2 = 1 := fun e =>
      (cayleySpinor_ok (unitDir_norm_sq (x.2 e.1.1 e.1.2 e.2.1)) (he_z e)).1
    have hmul : ∀ e, (pauliDot (eDir e)).mulVec (Φe e) = Φe e := fun e =>
      (cayleySpinor_ok (unitDir_norm_sq (x.2 e.1.1 e.1.2 e.2.1)) (he_z e)).2
    let d : Fin 2 → ℂ := cayleySpinor ![1, 0]
    have hd : ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 = 1 := by
      have h0 : d 0 = (((1 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ) := by
        simp [d, cayleySpinor]
      have h1 : d 1 = (((1 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) / ((Real.sqrt 2 : ℝ) : ℂ) := by
        simp [d, cayleySpinor]
      rw [h0, h1, cayley_comp_norm_sq 1 0]
      norm_num
    let Φ : ℕ → Fin 2 → ℂ := fun k => if h : k < m then Φe (pathNEdges m ⟨k, h⟩) else d
    have hunit : ∀ e, ‖Φ e 0‖ ^ 2 + ‖Φ e 1‖ ^ 2 = 1 := pathSpinorExt_unit m Φe hnorm hd
    have hreal : ∀ i j, (spIn (Φ i) (Φ j)).im = 0 := fun i j => by
      have hΦ_eq : ∀ k, Φ k = cayleySpinor (if h : k < m then cayleyPlanarHalf (eDir (pathNEdges m ⟨k, h⟩)) else ![1, 0]) := fun k => by
        by_cases h : k < m
        · simp only [Φ, h, ↓reduceDIte, Φe]
        · simp only [Φ, h, ↓reduceDIte, d]
      rw [hΦ_eq i, hΦ_eq j]
      exact cayleySpinor_spIn_im_zero _ _
    rw [pathGraphN_gram_eq_pathGramSum m x Φe hnorm hmul d, Complex.conj_re,
      pathGramSum_eq_rec Φ hunit m hm]
    have him : (pathRecPair Φ m).1.im = 0 := by
      rw [← pathGramSum_eq_rec Φ hunit m hm]
      exact pathGramSum_im_zero_of_spIn_real Φ hreal m
    have hpos := pathRecPair_planar_pos Φ hunit hreal m hm
    have hhyp := pathRecPair_hyperbolic_ge_one Φ hunit m hm
    have hre_sq : 1 ≤ (pathRecPair Φ m).1.re ^ 2 := by
      have hn : ‖(pathRecPair Φ m).1‖ ^ 2 = (pathRecPair Φ m).1.re ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him, mul_zero, add_zero, sq]
      linarith [sq_nonneg ‖pathBeta Φ m‖]
    nlinarith [hpos]

end PlanarPathConjectureC

end Matematyka.MalkounPathPositivity


