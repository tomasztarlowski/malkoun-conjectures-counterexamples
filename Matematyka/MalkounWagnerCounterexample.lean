import Matematyka.MalkounN7Counterexample

/-!
# Formal Disproof of Malkoun's Conjectures on the Triangle-Free 3-Connected Cubic Wagner Graph $M_8$

We formalize the integer planar witness for the 8-vertex, 12-edge cubic M\"obius ladder
$M_8$ (`wagnerGraph`), which is 3-vertex-connected (`IsThreeVertexConnected wagnerGraph`),
3-regular (`wagnerGraph.IsRegularOfDegree 3`), and triangle-free (`wagnerGraph.CliqueFree 3`).
Using an exact 4-block decomposition (`B0={0,4}, B1={3,7}, B2={1,2}, B3={5,6}`),
exact collinear Gaussian-integer reduction at $t = 0$ (`+2304`), closed integer interval
arithmetic at scale $S = 10^6$ (`IntIv`/`CIntIv`) at $t = 1$, and continuity + IVT,
we refute Malkoun's Conjectures A, B, and Section 6 even on 3-connected triangle-free graphs.
-/

namespace Matematyka.MalkounWagnerCounterexample

open Complex Matematyka.MalkounCounterexample Matematyka.MalkounN7Counterexample

private lemma fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

/-! ## Part 1: Wagner Graph $M_8$, 3-Vertex Connectivity, 3-Regularity, and Triangle-Freeness -/

section GraphProperties

/-- Boolean adjacency predicate on `Fin 8` for the Wagner graph $M_8$ ($m = 12$). -/
def wagnerAdjBool (u v : Fin 8) : Bool :=
  (u != v) &&
    (((u.val == 0 && v.val == 1) || (u.val == 1 && v.val == 0)) ||
     ((u.val == 0 && v.val == 4) || (u.val == 4 && v.val == 0)) ||
     ((u.val == 0 && v.val == 7) || (u.val == 7 && v.val == 0)) ||
     ((u.val == 1 && v.val == 2) || (u.val == 2 && v.val == 1)) ||
     ((u.val == 1 && v.val == 5) || (u.val == 5 && v.val == 1)) ||
     ((u.val == 2 && v.val == 3) || (u.val == 3 && v.val == 2)) ||
     ((u.val == 2 && v.val == 6) || (u.val == 6 && v.val == 2)) ||
     ((u.val == 3 && v.val == 4) || (u.val == 4 && v.val == 3)) ||
     ((u.val == 3 && v.val == 7) || (u.val == 7 && v.val == 3)) ||
     ((u.val == 4 && v.val == 5) || (u.val == 5 && v.val == 4)) ||
     ((u.val == 5 && v.val == 6) || (u.val == 6 && v.val == 5)) ||
     ((u.val == 6 && v.val == 7) || (u.val == 7 && v.val == 6)))

/-- The 8-vertex, 12-edge cubic M\"obius ladder $M_8$ (Wagner graph). -/
def wagnerGraph : SimpleGraph (Fin 8) where
  Adj u v := wagnerAdjBool u v = true
  symm := by
    have h : ∀ u v : Fin 8, wagnerAdjBool u v = true → wagnerAdjBool v u = true := by decide
    exact ⟨h⟩
  loopless := by
    have h : ∀ u : Fin 8, wagnerAdjBool u u ≠ true := by decide
    exact ⟨h⟩

instance instDecidableRelWagner : DecidableRel wagnerGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (wagnerAdjBool u v = true))

theorem wagnerGraph_connected : wagnerGraph.Connected := by
  refine ⟨fun u v => ?_⟩
  have h0 : ∀ w : Fin 8, wagnerGraph.Reachable 0 w := by
    intro w
    fin_cases w
    · exact SimpleGraph.Reachable.refl 0
    · exact SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 0 1)
    · exact (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 0 1)).trans
        (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 1 2))
    · exact (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 0 4)).trans
        (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 4 3))
    · exact SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 0 4)
    · exact (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 0 4)).trans
        (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 4 5))
    · exact (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 0 7)).trans
        (SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 7 6))
    · exact SimpleGraph.Adj.reachable (by decide : wagnerGraph.Adj 0 7)
  exact (h0 u).symm.trans (h0 v)

/-- A finite simple graph on `Fin n` is **3-vertex-connected** ($\kappa(G) \ge 3$) when
$n \ge 4$, $G$ is connected, and deleting any two vertices leaves a connected graph. -/
def IsThreeVertexConnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  4 ≤ n ∧ G.Connected ∧ ∀ c₁ c₂ : Fin n, (G.induce {x : Fin n | x ≠ c₁ ∧ x ≠ c₂}).Connected

private def wagnerAnchor (c₁ c₂ : Fin 8) : Fin 8 :=
  if (0 : Fin 8) ≠ c₁ ∧ (0 : Fin 8) ≠ c₂ then 0
  else if (1 : Fin 8) ≠ c₁ ∧ (1 : Fin 8) ≠ c₂ then 1
  else 2

private lemma wagnerAnchor_mem : ∀ c₁ c₂ : Fin 8,
    wagnerAnchor c₁ c₂ ≠ c₁ ∧ wagnerAnchor c₁ c₂ ≠ c₂ := by decide

private def isValidInducedWalk (c₁ c₂ : Fin 8) : Fin 8 → List (Fin 8) → Fin 8 → Bool
  | a, [], b => a == b
  | a, x :: xs, b =>
      wagnerAdjBool a x && (x != c₁) && (x != c₂) && isValidInducedWalk c₁ c₂ x xs b

private lemma reachable_of_isValidInducedWalk (c₁ c₂ : Fin 8) :
    ∀ (l : List (Fin 8)) (a b : Fin 8) (ha : a ≠ c₁ ∧ a ≠ c₂) (hb : b ≠ c₁ ∧ b ≠ c₂),
      isValidInducedWalk c₁ c₂ a l b = true →
      (wagnerGraph.induce {x : Fin 8 | x ≠ c₁ ∧ x ≠ c₂}).Reachable ⟨a, ha⟩ ⟨b, hb⟩
  | [], a, b, ha, hb, h => by
      simp only [isValidInducedWalk, beq_iff_eq] at h
      subst h
      exact SimpleGraph.Reachable.refl _
  | x :: xs, a, b, ha, hb, h => by
      simp only [isValidInducedWalk, Bool.and_eq_true, bne_iff_ne] at h
      rcases h with ⟨⟨⟨hadj, hxc1⟩, hxc2⟩, hrest⟩
      have hx : x ≠ c₁ ∧ x ≠ c₂ := ⟨hxc1, hxc2⟩
      have hedge : (wagnerGraph.induce {v : Fin 8 | v ≠ c₁ ∧ v ≠ c₂}).Adj ⟨a, ha⟩ ⟨x, hx⟩ := hadj
      exact hedge.reachable.trans (reachable_of_isValidInducedWalk c₁ c₂ xs x b hx hb hrest)

private def wagnerWalk (c₁ c₂ b : Fin 8) : List (Fin 8) :=
  let a := min c₁.val c₂.val
  let d := max c₁.val c₂.val
  match a, d, b.val with
  | 0, 0, 2 => [2]
  | 0, 0, 3 => [2, 3]
  | 0, 0, 4 => [5, 4]
  | 0, 0, 5 => [5]
  | 0, 0, 6 => [2, 6]
  | 0, 0, 7 => [2, 3, 7]
  | 0, 1, 3 => [3]
  | 0, 1, 4 => [3, 4]
  | 0, 1, 5 => [6, 5]
  | 0, 1, 6 => [6]
  | 0, 1, 7 => [3, 7]
  | 0, 2, 3 => [5, 4, 3]
  | 0, 2, 4 => [5, 4]
  | 0, 2, 5 => [5]
  | 0, 2, 6 => [5, 6]
  | 0, 2, 7 => [5, 6, 7]
  | 0, 3, 2 => [2]
  | 0, 3, 4 => [5, 4]
  | 0, 3, 5 => [5]
  | 0, 3, 6 => [2, 6]
  | 0, 3, 7 => [2, 6, 7]
  | 0, 4, 2 => [2]
  | 0, 4, 3 => [2, 3]
  | 0, 4, 5 => [5]
  | 0, 4, 6 => [2, 6]
  | 0, 4, 7 => [2, 3, 7]
  | 0, 5, 2 => [2]
  | 0, 5, 3 => [2, 3]
  | 0, 5, 4 => [2, 3, 4]
  | 0, 5, 6 => [2, 6]
  | 0, 5, 7 => [2, 3, 7]
  | 0, 6, 2 => [2]
  | 0, 6, 3 => [2, 3]
  | 0, 6, 4 => [5, 4]
  | 0, 6, 5 => [5]
  | 0, 6, 7 => [2, 3, 7]
  | 0, 7, 2 => [2]
  | 0, 7, 3 => [2, 3]
  | 0, 7, 4 => [5, 4]
  | 0, 7, 5 => [5]
  | 0, 7, 6 => [2, 6]
  | 1, 1, 2 => [4, 3, 2]
  | 1, 1, 3 => [4, 3]
  | 1, 1, 4 => [4]
  | 1, 1, 5 => [4, 5]
  | 1, 1, 6 => [7, 6]
  | 1, 1, 7 => [7]
  | 1, 2, 3 => [4, 3]
  | 1, 2, 4 => [4]
  | 1, 2, 5 => [4, 5]
  | 1, 2, 6 => [7, 6]
  | 1, 2, 7 => [7]
  | 1, 3, 2 => [7, 6, 2]
  | 1, 3, 4 => [4]
  | 1, 3, 5 => [4, 5]
  | 1, 3, 6 => [7, 6]
  | 1, 3, 7 => [7]
  | 1, 4, 2 => [7, 3, 2]
  | 1, 4, 3 => [7, 3]
  | 1, 4, 5 => [7, 6, 5]
  | 1, 4, 6 => [7, 6]
  | 1, 4, 7 => [7]
  | 1, 5, 2 => [4, 3, 2]
  | 1, 5, 3 => [4, 3]
  | 1, 5, 4 => [4]
  | 1, 5, 6 => [7, 6]
  | 1, 5, 7 => [7]
  | 1, 6, 2 => [4, 3, 2]
  | 1, 6, 3 => [4, 3]
  | 1, 6, 4 => [4]
  | 1, 6, 5 => [4, 5]
  | 1, 6, 7 => [7]
  | 1, 7, 2 => [4, 3, 2]
  | 1, 7, 3 => [4, 3]
  | 1, 7, 4 => [4]
  | 1, 7, 5 => [4, 5]
  | 1, 7, 6 => [4, 5, 6]
  | 2, 2, 1 => [1]
  | 2, 2, 3 => [4, 3]
  | 2, 2, 4 => [4]
  | 2, 2, 5 => [1, 5]
  | 2, 2, 6 => [7, 6]
  | 2, 2, 7 => [7]
  | 2, 3, 1 => [1]
  | 2, 3, 4 => [4]
  | 2, 3, 5 => [1, 5]
  | 2, 3, 6 => [7, 6]
  | 2, 3, 7 => [7]
  | 2, 4, 1 => [1]
  | 2, 4, 3 => [7, 3]
  | 2, 4, 5 => [1, 5]
  | 2, 4, 6 => [7, 6]
  | 2, 4, 7 => [7]
  | 2, 5, 1 => [1]
  | 2, 5, 3 => [4, 3]
  | 2, 5, 4 => [4]
  | 2, 5, 6 => [7, 6]
  | 2, 5, 7 => [7]
  | 2, 6, 1 => [1]
  | 2, 6, 3 => [4, 3]
  | 2, 6, 4 => [4]
  | 2, 6, 5 => [1, 5]
  | 2, 6, 7 => [7]
  | 2, 7, 1 => [1]
  | 2, 7, 3 => [4, 3]
  | 2, 7, 4 => [4]
  | 2, 7, 5 => [1, 5]
  | 2, 7, 6 => [1, 5, 6]
  | 3, 3, 1 => [1]
  | 3, 3, 2 => [1, 2]
  | 3, 3, 4 => [4]
  | 3, 3, 5 => [1, 5]
  | 3, 3, 6 => [7, 6]
  | 3, 3, 7 => [7]
  | 3, 4, 1 => [1]
  | 3, 4, 2 => [1, 2]
  | 3, 4, 5 => [1, 5]
  | 3, 4, 6 => [7, 6]
  | 3, 4, 7 => [7]
  | 3, 5, 1 => [1]
  | 3, 5, 2 => [1, 2]
  | 3, 5, 4 => [4]
  | 3, 5, 6 => [7, 6]
  | 3, 5, 7 => [7]
  | 3, 6, 1 => [1]
  | 3, 6, 2 => [1, 2]
  | 3, 6, 4 => [4]
  | 3, 6, 5 => [1, 5]
  | 3, 6, 7 => [7]
  | 3, 7, 1 => [1]
  | 3, 7, 2 => [1, 2]
  | 3, 7, 4 => [4]
  | 3, 7, 5 => [1, 5]
  | 3, 7, 6 => [1, 2, 6]
  | 4, 4, 1 => [1]
  | 4, 4, 2 => [1, 2]
  | 4, 4, 3 => [7, 3]
  | 4, 4, 5 => [1, 5]
  | 4, 4, 6 => [7, 6]
  | 4, 4, 7 => [7]
  | 4, 5, 1 => [1]
  | 4, 5, 2 => [1, 2]
  | 4, 5, 3 => [7, 3]
  | 4, 5, 6 => [7, 6]
  | 4, 5, 7 => [7]
  | 4, 6, 1 => [1]
  | 4, 6, 2 => [1, 2]
  | 4, 6, 3 => [7, 3]
  | 4, 6, 5 => [1, 5]
  | 4, 6, 7 => [7]
  | 4, 7, 1 => [1]
  | 4, 7, 2 => [1, 2]
  | 4, 7, 3 => [1, 2, 3]
  | 4, 7, 5 => [1, 5]
  | 4, 7, 6 => [1, 2, 6]
  | 5, 5, 1 => [1]
  | 5, 5, 2 => [1, 2]
  | 5, 5, 3 => [4, 3]
  | 5, 5, 4 => [4]
  | 5, 5, 6 => [7, 6]
  | 5, 5, 7 => [7]
  | 5, 6, 1 => [1]
  | 5, 6, 2 => [1, 2]
  | 5, 6, 3 => [4, 3]
  | 5, 6, 4 => [4]
  | 5, 6, 7 => [7]
  | 5, 7, 1 => [1]
  | 5, 7, 2 => [1, 2]
  | 5, 7, 3 => [4, 3]
  | 5, 7, 4 => [4]
  | 5, 7, 6 => [1, 2, 6]
  | 6, 6, 1 => [1]
  | 6, 6, 2 => [1, 2]
  | 6, 6, 3 => [4, 3]
  | 6, 6, 4 => [4]
  | 6, 6, 5 => [1, 5]
  | 6, 6, 7 => [7]
  | 6, 7, 1 => [1]
  | 6, 7, 2 => [1, 2]
  | 6, 7, 3 => [4, 3]
  | 6, 7, 4 => [4]
  | 6, 7, 5 => [1, 5]
  | 7, 7, 1 => [1]
  | 7, 7, 2 => [1, 2]
  | 7, 7, 3 => [4, 3]
  | 7, 7, 4 => [4]
  | 7, 7, 5 => [1, 5]
  | 7, 7, 6 => [1, 2, 6]
  | _, _, _ => []

private lemma wagnerWalk_valid : ∀ c₁ c₂ b : Fin 8, b ≠ c₁ → b ≠ c₂ →
    isValidInducedWalk c₁ c₂ (wagnerAnchor c₁ c₂) (wagnerWalk c₁ c₂ b) b = true := by decide

/-- `wagnerGraph` is 3-vertex-connected ($\kappa(M_8) = 3$). -/
theorem wagnerGraph_threeVertexConnected : IsThreeVertexConnected wagnerGraph := by
  refine ⟨by norm_num, wagnerGraph_connected, fun c₁ c₂ => ?_⟩
  let anchor := wagnerAnchor c₁ c₂
  have ha : anchor ≠ c₁ ∧ anchor ≠ c₂ := wagnerAnchor_mem c₁ c₂
  have : Nonempty {x : Fin 8 | x ≠ c₁ ∧ x ≠ c₂} := ⟨⟨anchor, ha⟩⟩
  refine ⟨fun u v => ?_⟩
  have hru : (wagnerGraph.induce {x : Fin 8 | x ≠ c₁ ∧ x ≠ c₂}).Reachable ⟨anchor, ha⟩ u :=
    reachable_of_isValidInducedWalk c₁ c₂ (wagnerWalk c₁ c₂ u.1) anchor u.1 ha u.2
      (wagnerWalk_valid c₁ c₂ u.1 u.2.1 u.2.2)
  have hrv : (wagnerGraph.induce {x : Fin 8 | x ≠ c₁ ∧ x ≠ c₂}).Reachable ⟨anchor, ha⟩ v :=
    reachable_of_isValidInducedWalk c₁ c₂ (wagnerWalk c₁ c₂ v.1) anchor v.1 ha v.2
      (wagnerWalk_valid c₁ c₂ v.1 v.2.1 v.2.2)
  exact hru.symm.trans hrv

/-- `wagnerGraph` is cubic (3-regular). -/
theorem wagnerGraph_isRegularOfDegree_three : wagnerGraph.IsRegularOfDegree 3 := by
  intro u
  fin_cases u <;> decide

private lemma wagner_no_triangle : ∀ a b c : Fin 8,
    ¬ (wagnerAdjBool a b = true ∧ wagnerAdjBool b c = true ∧ wagnerAdjBool a c = true) := by decide

/-- `wagnerGraph` is triangle-free (`CliqueFree 3`, girth 4). -/
theorem wagnerGraph_cliqueFree_three : wagnerGraph.CliqueFree 3 := by
  intro s hs
  rcases Finset.card_eq_three.mp hs.card_eq with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hc := hs.isClique
  exact wagner_no_triangle a b c ⟨hc (by simp) (by simp) hab, hc (by simp) (by simp) hbc, hc (by simp) (by simp) hac⟩

end GraphProperties

/-! ## Part 2: Exact 4-Block Decomposition of `malkounNum wagnerGraph` -/

section WagnerDecomposition

def wagnerNbr : Fin 8 → Fin 3 → Fin 8
  | 0, 0 => 1 | 0, 1 => 4 | 0, 2 => 7
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 5
  | 2, 0 => 1 | 2, 1 => 3 | 2, 2 => 6
  | 3, 0 => 2 | 3, 1 => 4 | 3, 2 => 7
  | 4, 0 => 0 | 4, 1 => 3 | 4, 2 => 5
  | 5, 0 => 1 | 5, 1 => 4 | 5, 2 => 6
  | 6, 0 => 2 | 6, 1 => 5 | 6, 2 => 7
  | 7, 0 => 0 | 7, 1 => 3 | 7, 2 => 6

def wagnerNbrIdx : Fin 8 → Fin 8 → Fin 3
  | 0, 1 => 0 | 0, 4 => 1 | 0, 7 => 2
  | 1, 0 => 0 | 1, 2 => 1 | 1, 5 => 2
  | 2, 1 => 0 | 2, 3 => 1 | 2, 6 => 2
  | 3, 2 => 0 | 3, 4 => 1 | 3, 7 => 2
  | 4, 0 => 0 | 4, 3 => 1 | 4, 5 => 2
  | 5, 1 => 0 | 5, 4 => 1 | 5, 6 => 2
  | 6, 2 => 0 | 6, 5 => 1 | 6, 7 => 2
  | 7, 0 => 0 | 7, 3 => 1 | 7, 6 => 2
  | _, _ => 0

private lemma wagnerNbr_adj : ∀ u : Fin 8, ∀ j : Fin 3, wagnerGraph.Adj u (wagnerNbr u j) := by
  decide

private lemma wagnerNbr_left_inv : ∀ u : Fin 8, ∀ j : Fin 3, wagnerNbrIdx u (wagnerNbr u j) = j := by
  decide

private lemma wagnerNbr_right_inv : ∀ u w : Fin 8, wagnerGraph.Adj u w → wagnerNbr u (wagnerNbrIdx u w) = w := by
  decide

private def wagnerNbrEquiv (u : Fin 8) : Fin 3 ≃ { w : Fin 8 // wagnerGraph.Adj u w } where
  toFun j := ⟨wagnerNbr u j, wagnerNbr_adj u j⟩
  invFun x := wagnerNbrIdx u x.1
  left_inv := wagnerNbr_left_inv u
  right_inv x := Subtype.ext (wagnerNbr_right_inv u x.1 x.2)

def perm3Fun : Fin 6 → Fin 3 → Fin 3
  | 0, x => x
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 2
  | 2, 0 => 2 | 2, 1 => 1 | 2, 2 => 0
  | 3, 0 => 0 | 3, 1 => 2 | 3, 2 => 1
  | 4, 0 => 1 | 4, 1 => 2 | 4, 2 => 0
  | 5, 0 => 2 | 5, 1 => 0 | 5, 2 => 1

private def perm3InvFun : Fin 6 → Fin 3 → Fin 3
  | 4 => perm3Fun 5
  | 5 => perm3Fun 4
  | i => perm3Fun i

private lemma perm3_left_inv : ∀ i : Fin 6, ∀ x : Fin 3, perm3InvFun i (perm3Fun i x) = x := by decide
private lemma perm3_right_inv : ∀ i : Fin 6, ∀ x : Fin 3, perm3Fun i (perm3InvFun i x) = x := by decide
private lemma perm3_inj : ∀ i j : Fin 6, (∀ x : Fin 3, perm3Fun i x = perm3Fun j x) → i = j := by decide

private def perm3ToEquiv (i : Fin 6) : Equiv.Perm (Fin 3) where
  toFun := perm3Fun i
  invFun := perm3InvFun i
  left_inv := perm3_left_inv i
  right_inv := perm3_right_inv i

private noncomputable def perm3Equiv : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective perm3ToEquiv <| (Fintype.bijective_iff_injective_and_card perm3ToEquiv).mpr <| by
    refine ⟨fun i j hij => perm3_inj i j fun x => congrFun (congrArg Equiv.toFun hij) x, ?_⟩
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num

private abbrev Block2Idx := Fin 6 × Fin 6
private abbrev Half8Idx := Block2Idx × Block2Idx
private abbrev WagnerPermIdx := Half8Idx × Half8Idx

private def pickVert8 (p : WagnerPermIdx) : Fin 8 → Fin 6
  | 0 => p.1.1.1 | 4 => p.1.1.2
  | 3 => p.1.2.1 | 7 => p.1.2.2
  | 1 => p.2.1.1 | 2 => p.2.1.2
  | 5 => p.2.2.1 | 6 => p.2.2.2

private def vert8PiEquiv : WagnerPermIdx ≃ (∀ _ : Fin 8, Fin 6) where
  toFun := pickVert8
  invFun f := (((f 0, f 4), (f 3, f 7)), ((f 1, f 2), (f 5, f 6)))
  left_inv p := by rcases p with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨⟨e, f⟩, ⟨g, h⟩⟩⟩; rfl
  right_inv f := by ext u; fin_cases u <;> rfl

private noncomputable def wagnerSourceEquiv : WagnerPermIdx ≃ SourcePerm wagnerGraph :=
  vert8PiEquiv.trans (Equiv.piCongrRight fun u =>
    perm3Equiv.trans (Equiv.permCongr (wagnerNbrEquiv u)))

private lemma wagnerSourceEquiv_apply (p : WagnerPermIdx) (u w : Fin 8) (hw : wagnerGraph.Adj u w) :
    ((wagnerSourceEquiv p u ⟨w, hw⟩).1) = wagnerNbr u (perm3Fun (pickVert8 p u) (wagnerNbrIdx u w)) := rfl

private lemma wagnerSourceEquiv_apply' (p : WagnerPermIdx) (u : Fin 8) (y : { w : Fin 8 // wagnerGraph.Adj u w }) :
    ((wagnerSourceEquiv p u y).1) = wagnerNbr u (perm3Fun (pickVert8 p u) (wagnerNbrIdx u y.1)) := rfl

def wagnerInternalEdges : Fin 4 → Fin 8 × Fin 8 := ![(0, 4), (3, 7), (1, 2), (5, 6)]
def wagnerIntraLeftEdges : Fin 2 → Fin 8 × Fin 8 := ![(0, 7), (3, 4)]
def wagnerIntraRightEdges : Fin 2 → Fin 8 × Fin 8 := ![(1, 5), (2, 6)]
def wagnerCutEdges : Fin 4 → Fin 8 × Fin 8 := ![(0, 1), (2, 3), (4, 5), (6, 7)]

private lemma wagnerInternalEdges_ok : ∀ i : Fin 4, wagnerGraph.Adj (wagnerInternalEdges i).1 (wagnerInternalEdges i).2 ∧ (wagnerInternalEdges i).1 < (wagnerInternalEdges i).2 := by decide
private lemma wagnerIntraLeftEdges_ok : ∀ i : Fin 2, wagnerGraph.Adj (wagnerIntraLeftEdges i).1 (wagnerIntraLeftEdges i).2 ∧ (wagnerIntraLeftEdges i).1 < (wagnerIntraLeftEdges i).2 := by decide
private lemma wagnerIntraRightEdges_ok : ∀ i : Fin 2, wagnerGraph.Adj (wagnerIntraRightEdges i).1 (wagnerIntraRightEdges i).2 ∧ (wagnerIntraRightEdges i).1 < (wagnerIntraRightEdges i).2 := by decide
private lemma wagnerCutEdges_ok : ∀ i : Fin 4, wagnerGraph.Adj (wagnerCutEdges i).1 (wagnerCutEdges i).2 ∧ (wagnerCutEdges i).1 < (wagnerCutEdges i).2 := by decide

private abbrev WagnerEdgeSlot := Fin 4 ⊕ Fin 2 ⊕ Fin 2 ⊕ Fin 4

private def wagnerOriToFun : WagnerEdgeSlot → OriEdge wagnerGraph
  | .inl i => ⟨wagnerInternalEdges i, (wagnerInternalEdges_ok i).1, (wagnerInternalEdges_ok i).2⟩
  | .inr (.inl i) => ⟨wagnerIntraLeftEdges i, (wagnerIntraLeftEdges_ok i).1, (wagnerIntraLeftEdges_ok i).2⟩
  | .inr (.inr (.inl i)) => ⟨wagnerIntraRightEdges i, (wagnerIntraRightEdges_ok i).1, (wagnerIntraRightEdges_ok i).2⟩
  | .inr (.inr (.inr i)) => ⟨wagnerCutEdges i, (wagnerCutEdges_ok i).1, (wagnerCutEdges_ok i).2⟩

private def wagnerOriInvFun (e : OriEdge wagnerGraph) : WagnerEdgeSlot :=
  match e.1.1.val, e.1.2.val with
  | 0, 4 => .inl 0 | 3, 7 => .inl 1 | 1, 2 => .inl 2 | 5, 6 => .inl 3
  | 0, 7 => .inr (.inl 0) | 3, 4 => .inr (.inl 1)
  | 1, 5 => .inr (.inr (.inl 0)) | 2, 6 => .inr (.inr (.inl 1))
  | 0, 1 => .inr (.inr (.inr 0)) | 2, 3 => .inr (.inr (.inr 1))
  | 4, 5 => .inr (.inr (.inr 2)) | 6, 7 => .inr (.inr (.inr 3))
  | _, _ => .inl 0

private def wagnerOriEquiv : WagnerEdgeSlot ≃ OriEdge wagnerGraph where
  toFun := wagnerOriToFun
  invFun := wagnerOriInvFun
  left_inv x := by rcases x with i | (i | (i | i)) <;> fin_cases i <;> rfl
  right_inv e := by
    rcases e with ⟨⟨u, v⟩, hadj, hlt⟩
    fin_cases u <;> fin_cases v <;> first | exact False.elim ((by decide : ¬(wagnerGraph.Adj _ _ ∧ _ < _)) ⟨hadj, hlt⟩) | rfl

private lemma wagnerOri_term_inl (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (σ : SourcePerm wagnerGraph) (i : Fin 4) :
    omega (ψ (wagnerOriEquiv (.inl i)).1.1 (σ (wagnerOriEquiv (.inl i)).1.1 ⟨(wagnerOriEquiv (.inl i)).1.2, (wagnerOriEquiv (.inl i)).2.1⟩).1)
          (ψ (wagnerOriEquiv (.inl i)).1.2 (σ (wagnerOriEquiv (.inl i)).1.2 ⟨(wagnerOriEquiv (.inl i)).1.1, (wagnerOriEquiv (.inl i)).2.1.symm⟩).1) =
    omega (ψ (wagnerInternalEdges i).1 (σ (wagnerInternalEdges i).1 ⟨(wagnerInternalEdges i).2, (wagnerInternalEdges_ok i).1⟩).1)
          (ψ (wagnerInternalEdges i).2 (σ (wagnerInternalEdges i).2 ⟨(wagnerInternalEdges i).1, (wagnerInternalEdges_ok i).1.symm⟩).1) := rfl

private lemma wagnerOri_term_inrl (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (σ : SourcePerm wagnerGraph) (i : Fin 2) :
    omega (ψ (wagnerOriEquiv (.inr (.inl i))).1.1 (σ (wagnerOriEquiv (.inr (.inl i))).1.1 ⟨(wagnerOriEquiv (.inr (.inl i))).1.2, (wagnerOriEquiv (.inr (.inl i))).2.1⟩).1)
          (ψ (wagnerOriEquiv (.inr (.inl i))).1.2 (σ (wagnerOriEquiv (.inr (.inl i))).1.2 ⟨(wagnerOriEquiv (.inr (.inl i))).1.1, (wagnerOriEquiv (.inr (.inl i))).2.1.symm⟩).1) =
    omega (ψ (wagnerIntraLeftEdges i).1 (σ (wagnerIntraLeftEdges i).1 ⟨(wagnerIntraLeftEdges i).2, (wagnerIntraLeftEdges_ok i).1⟩).1)
          (ψ (wagnerIntraLeftEdges i).2 (σ (wagnerIntraLeftEdges i).2 ⟨(wagnerIntraLeftEdges i).1, (wagnerIntraLeftEdges_ok i).1.symm⟩).1) := rfl

private lemma wagnerOri_term_inrrl (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (σ : SourcePerm wagnerGraph) (i : Fin 2) :
    omega (ψ (wagnerOriEquiv (.inr (.inr (.inl i)))).1.1 (σ (wagnerOriEquiv (.inr (.inr (.inl i)))).1.1 ⟨(wagnerOriEquiv (.inr (.inr (.inl i)))).1.2, (wagnerOriEquiv (.inr (.inr (.inl i)))).2.1⟩).1)
          (ψ (wagnerOriEquiv (.inr (.inr (.inl i)))).1.2 (σ (wagnerOriEquiv (.inr (.inr (.inl i)))).1.2 ⟨(wagnerOriEquiv (.inr (.inr (.inl i)))).1.1, (wagnerOriEquiv (.inr (.inr (.inl i)))).2.1.symm⟩).1) =
    omega (ψ (wagnerIntraRightEdges i).1 (σ (wagnerIntraRightEdges i).1 ⟨(wagnerIntraRightEdges i).2, (wagnerIntraRightEdges_ok i).1⟩).1)
          (ψ (wagnerIntraRightEdges i).2 (σ (wagnerIntraRightEdges i).2 ⟨(wagnerIntraRightEdges i).1, (wagnerIntraRightEdges_ok i).1.symm⟩).1) := rfl

private lemma wagnerOri_term_inrrr (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (σ : SourcePerm wagnerGraph) (i : Fin 4) :
    omega (ψ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.1 (σ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.1 ⟨(wagnerOriEquiv (.inr (.inr (.inr i)))).1.2, (wagnerOriEquiv (.inr (.inr (.inr i)))).2.1⟩).1)
          (ψ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.2 (σ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.2 ⟨(wagnerOriEquiv (.inr (.inr (.inr i)))).1.1, (wagnerOriEquiv (.inr (.inr (.inr i)))).2.1.symm⟩).1) =
    omega (ψ (wagnerCutEdges i).1 (σ (wagnerCutEdges i).1 ⟨(wagnerCutEdges i).2, (wagnerCutEdges_ok i).1⟩).1)
          (ψ (wagnerCutEdges i).2 (σ (wagnerCutEdges i).2 ⟨(wagnerCutEdges i).1, (wagnerCutEdges_ok i).1.symm⟩).1) := rfl

private lemma wagnerOri_den_inl (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (i : Fin 4) :
    omega (ψ (wagnerOriEquiv (.inl i)).1.1 (wagnerOriEquiv (.inl i)).1.2)
          (ψ (wagnerOriEquiv (.inl i)).1.2 (wagnerOriEquiv (.inl i)).1.1) =
    omega (ψ (wagnerInternalEdges i).1 (wagnerInternalEdges i).2)
          (ψ (wagnerInternalEdges i).2 (wagnerInternalEdges i).1) := rfl

private lemma wagnerOri_den_inrl (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (i : Fin 2) :
    omega (ψ (wagnerOriEquiv (.inr (.inl i))).1.1 (wagnerOriEquiv (.inr (.inl i))).1.2)
          (ψ (wagnerOriEquiv (.inr (.inl i))).1.2 (wagnerOriEquiv (.inr (.inl i))).1.1) =
    omega (ψ (wagnerIntraLeftEdges i).1 (wagnerIntraLeftEdges i).2)
          (ψ (wagnerIntraLeftEdges i).2 (wagnerIntraLeftEdges i).1) := rfl

private lemma wagnerOri_den_inrrl (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (i : Fin 2) :
    omega (ψ (wagnerOriEquiv (.inr (.inr (.inl i)))).1.1 (wagnerOriEquiv (.inr (.inr (.inl i)))).1.2)
          (ψ (wagnerOriEquiv (.inr (.inr (.inl i)))).1.2 (wagnerOriEquiv (.inr (.inr (.inl i)))).1.1) =
    omega (ψ (wagnerIntraRightEdges i).1 (wagnerIntraRightEdges i).2)
          (ψ (wagnerIntraRightEdges i).2 (wagnerIntraRightEdges i).1) := rfl

private lemma wagnerOri_den_inrrr (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (i : Fin 4) :
    omega (ψ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.1 (wagnerOriEquiv (.inr (.inr (.inr i)))).1.2)
          (ψ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.2 (wagnerOriEquiv (.inr (.inr (.inr i)))).1.1) =
    omega (ψ (wagnerCutEdges i).1 (wagnerCutEdges i).2)
          (ψ (wagnerCutEdges i).2 (wagnerCutEdges i).1) := rfl

private def invBit (b : Fin 2) : Fin 2 := 1 - b
private def sgnBitC (b : Fin 2) : ℂ := if b = 0 then 1 else -1
private def sgn2C (b : Fin 2 → Fin 2) : ℂ := sgnBitC (b 0) * sgnBitC (b 1)
private def sgn4C (b : Fin 4 → Fin 2) : ℂ := ∏ i : Fin 4, sgnBitC (b i)

private lemma invBit_val (b : Fin 2) : (invBit b).val = if b = 0 then 1 else 0 := by
  fin_cases b <;> decide

private lemma omega_eq_sub_bit (a b : Fin 2 → ℂ) :
    omega a b = a 0 * b (invBit 0) - a 1 * b (invBit 1) := by
  have h0 : invBit 0 = 1 := by decide
  have h1 : invBit 1 = 0 := by decide
  simp [omega, h0, h1]

private lemma prod_fin2_sub (m : ℕ) (f : Fin m → Fin 2 → ℂ) :
    (∏ i : Fin m, (f i 0 - f i 1)) = ∑ b : Fin m → Fin 2, (∏ i : Fin m, sgnBitC (b i) * f i (b i)) :=
  prod_fin2_sub_eq_sumBits m f

private lemma sum_prod2 {A B : Type*} [Fintype A] [Fintype B] (s : ℂ) (fa : A → ℂ) (fb : B → ℂ) :
    (∑ p : A × B, s * fa p.1 * fb p.2) = s * (∑ a, fa a) * (∑ b, fb b) := by
  rw [Fintype.sum_prod_type]
  calc ∑ a : A, ∑ b : B, s * fa a * fb b
      = ∑ a : A, s * fa a * ∑ b : B, fb b := Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ a : A, s * fa a) * ∑ b : B, fb b := (Finset.sum_mul _ _ _).symm
    _ = s * (∑ a : A, fa a) * ∑ b : B, fb b := congrArg (· * _) (Finset.mul_sum _ _ _).symm

/-- Generic 2-vertex block evaluation over all $6 \times 6 = 36$ local permutation pairs. -/
noncomputable def block2ValC (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ)
    (u v p0 p1 p2 p3 : Fin 8) (b0 b1 b2 b3 : Fin 2) : ℂ :=
  ∑ i : Fin 6, ∑ j : Fin 6,
    omega (ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u v))))
          (ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v u)))) *
    ((ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u p0))) b0 *
      ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u p1))) b1) *
     (ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v p2))) b2 *
      ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v p3))) b3))

noncomputable def leftHalf8C (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (c : Fin 4 → Fin 2) : ℂ :=
  sumBits 2 fun b =>
    sgn2C b *
      block2ValC ψ 0 4 1 7 3 5 (c 0) (b 0) (invBit (b 1)) (c 2) *
      block2ValC ψ 3 7 2 4 0 6 (invBit (c 1)) (b 1) (invBit (b 0)) (invBit (c 3))

noncomputable def rightHalf8C (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (c : Fin 4 → Fin 2) : ℂ :=
  sumBits 2 fun r =>
    sgn2C r *
      block2ValC ψ 1 2 0 5 3 6 (invBit (c 0)) (r 0) (c 1) (r 1) *
      block2ValC ψ 5 6 1 4 2 7 (invBit (r 0)) (invBit (c 2)) (invBit (r 1)) (c 3)

private lemma sum_bitFun_eq_sumBits : ∀ (m : ℕ) (f : (Fin m → Fin 2) → ℂ),
    (∑ b : Fin m → Fin 2, f b) = sumBits m f
  | 0, f => by rw [Fintype.sum_unique]; exact congrArg f (Subsingleton.elim _ _)
  | m + 1, f => by
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2))
        (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl), Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [sumBits, sum_bitFun_eq_sumBits m]

private def zeroHalf8 : Half8Idx := (((0 : Fin 6), (0 : Fin 6)), ((0 : Fin 6), (0 : Fin 6)))

private lemma wagner_left_block_eq (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (c : Fin 4 → Fin 2) :
    (∑ L : Half8Idx,
      let σ := wagnerSourceEquiv (L, zeroHalf8)
      (ψ 0 (σ 0 ⟨1, by decide⟩).1 (c 0) * ψ 3 (σ 3 ⟨2, by decide⟩).1 (invBit (c 1)) *
       ψ 4 (σ 4 ⟨5, by decide⟩).1 (c 2) * ψ 7 (σ 7 ⟨6, by decide⟩).1 (invBit (c 3))) *
      (omega (ψ 0 (σ 0 ⟨4, by decide⟩).1) (ψ 4 (σ 4 ⟨0, by decide⟩).1) *
       omega (ψ 3 (σ 3 ⟨7, by decide⟩).1) (ψ 7 (σ 7 ⟨3, by decide⟩).1) *
       omega (ψ 0 (σ 0 ⟨7, by decide⟩).1) (ψ 7 (σ 7 ⟨0, by decide⟩).1) *
       omega (ψ 3 (σ 3 ⟨4, by decide⟩).1) (ψ 4 (σ 4 ⟨3, by decide⟩).1))) = leftHalf8C ψ c := by
  have hL : ∀ L : Half8Idx,
      let σ := wagnerSourceEquiv (L, zeroHalf8)
      ((ψ 0 (σ 0 ⟨1, by decide⟩).1 (c 0) * ψ 3 (σ 3 ⟨2, by decide⟩).1 (invBit (c 1)) *
        ψ 4 (σ 4 ⟨5, by decide⟩).1 (c 2) * ψ 7 (σ 7 ⟨6, by decide⟩).1 (invBit (c 3))) *
       (omega (ψ 0 (σ 0 ⟨4, by decide⟩).1) (ψ 4 (σ 4 ⟨0, by decide⟩).1) *
        omega (ψ 3 (σ 3 ⟨7, by decide⟩).1) (ψ 7 (σ 7 ⟨3, by decide⟩).1) *
        omega (ψ 0 (σ 0 ⟨7, by decide⟩).1) (ψ 7 (σ 7 ⟨0, by decide⟩).1) *
        omega (ψ 3 (σ 3 ⟨4, by decide⟩).1) (ψ 4 (σ 4 ⟨3, by decide⟩).1))) =
      ∑ b : Fin 2 → Fin 2, sgn2C b *
        (omega (ψ 0 (wagnerNbr 0 (perm3Fun L.1.1 (wagnerNbrIdx 0 4))))
               (ψ 4 (wagnerNbr 4 (perm3Fun L.1.2 (wagnerNbrIdx 4 0)))) *
         ((ψ 0 (wagnerNbr 0 (perm3Fun L.1.1 (wagnerNbrIdx 0 1))) (c 0) *
           ψ 0 (wagnerNbr 0 (perm3Fun L.1.1 (wagnerNbrIdx 0 7))) (b 0)) *
          (ψ 4 (wagnerNbr 4 (perm3Fun L.1.2 (wagnerNbrIdx 4 3))) (invBit (b 1)) *
           ψ 4 (wagnerNbr 4 (perm3Fun L.1.2 (wagnerNbrIdx 4 5))) (c 2)))) *
        (omega (ψ 3 (wagnerNbr 3 (perm3Fun L.2.1 (wagnerNbrIdx 3 7))))
               (ψ 7 (wagnerNbr 7 (perm3Fun L.2.2 (wagnerNbrIdx 7 3)))) *
         ((ψ 3 (wagnerNbr 3 (perm3Fun L.2.1 (wagnerNbrIdx 3 2))) (invBit (c 1)) *
           ψ 3 (wagnerNbr 3 (perm3Fun L.2.1 (wagnerNbrIdx 3 4))) (b 1)) *
          (ψ 7 (wagnerNbr 7 (perm3Fun L.2.2 (wagnerNbrIdx 7 0))) (invBit (b 0)) *
           ψ 7 (wagnerNbr 7 (perm3Fun L.2.2 (wagnerNbrIdx 7 6))) (invBit (c 3))))) := by
    intro L
    let f : Fin 2 → Fin 2 → ℂ := fun i k => match i with
      | 0 => ψ 0 (wagnerNbr 0 (perm3Fun L.1.1 (wagnerNbrIdx 0 7))) k *
             ψ 7 (wagnerNbr 7 (perm3Fun L.2.2 (wagnerNbrIdx 7 0))) (invBit k)
      | 1 => ψ 3 (wagnerNbr 3 (perm3Fun L.2.1 (wagnerNbrIdx 3 4))) k *
             ψ 4 (wagnerNbr 4 (perm3Fun L.1.2 (wagnerNbrIdx 4 3))) (invBit k)
    have hf0 : omega (ψ 0 (wagnerNbr 0 (perm3Fun L.1.1 (wagnerNbrIdx 0 7))))
                     (ψ 7 (wagnerNbr 7 (perm3Fun L.2.2 (wagnerNbrIdx 7 0)))) = f 0 0 - f 0 1 :=
      omega_eq_sub_bit _ _
    have hf1 : omega (ψ 3 (wagnerNbr 3 (perm3Fun L.2.1 (wagnerNbrIdx 3 4))))
                     (ψ 4 (wagnerNbr 4 (perm3Fun L.1.2 (wagnerNbrIdx 4 3)))) = f 1 0 - f 1 1 :=
      omega_eq_sub_bit _ _
    have hsplit : (∏ i : Fin 2, (f i 0 - f i 1)) =
        ∑ b : Fin 2 → Fin 2, ∏ i : Fin 2, sgnBitC (b i) * f i (b i) := prod_fin2_sub 2 f
    dsimp only
    simp only [wagnerSourceEquiv_apply, pickVert8] at *
    rw [hf0, hf1, mul_assoc (omega _ _ * omega _ _), ← Fin.prod_univ_two (fun i => f i 0 - f i 1), hsplit, ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Fin.prod_univ_two, sgn2C, f]
    ring
  simp_rw [hL]
  rw [Finset.sum_comm]
  dsimp only [leftHalf8C]
  rw [← sum_bitFun_eq_sumBits 2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_prod2 (sgn2C b)
    (fun L1 : Block2Idx =>
      omega (ψ 0 (wagnerNbr 0 (perm3Fun L1.1 (wagnerNbrIdx 0 4))))
            (ψ 4 (wagnerNbr 4 (perm3Fun L1.2 (wagnerNbrIdx 4 0)))) *
      ((ψ 0 (wagnerNbr 0 (perm3Fun L1.1 (wagnerNbrIdx 0 1))) (c 0) *
        ψ 0 (wagnerNbr 0 (perm3Fun L1.1 (wagnerNbrIdx 0 7))) (b 0)) *
       (ψ 4 (wagnerNbr 4 (perm3Fun L1.2 (wagnerNbrIdx 4 3))) (invBit (b 1)) *
        ψ 4 (wagnerNbr 4 (perm3Fun L1.2 (wagnerNbrIdx 4 5))) (c 2))))
    (fun L2 : Block2Idx =>
      omega (ψ 3 (wagnerNbr 3 (perm3Fun L2.1 (wagnerNbrIdx 3 7))))
            (ψ 7 (wagnerNbr 7 (perm3Fun L2.2 (wagnerNbrIdx 7 3)))) *
      ((ψ 3 (wagnerNbr 3 (perm3Fun L2.1 (wagnerNbrIdx 3 2))) (invBit (c 1)) *
        ψ 3 (wagnerNbr 3 (perm3Fun L2.1 (wagnerNbrIdx 3 4))) (b 1)) *
       (ψ 7 (wagnerNbr 7 (perm3Fun L2.2 (wagnerNbrIdx 7 0))) (invBit (b 0)) *
        ψ 7 (wagnerNbr 7 (perm3Fun L2.2 (wagnerNbrIdx 7 6))) (invBit (c 3))))),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [block2ValC]

private lemma wagner_right_block_eq (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) (c : Fin 4 → Fin 2) :
    (∑ R : Half8Idx,
      let σ := wagnerSourceEquiv (zeroHalf8, R)
      (ψ 1 (σ 1 ⟨0, by decide⟩).1 (invBit (c 0)) * ψ 2 (σ 2 ⟨3, by decide⟩).1 (c 1) *
       ψ 5 (σ 5 ⟨4, by decide⟩).1 (invBit (c 2)) * ψ 6 (σ 6 ⟨7, by decide⟩).1 (c 3)) *
      (omega (ψ 1 (σ 1 ⟨2, by decide⟩).1) (ψ 2 (σ 2 ⟨1, by decide⟩).1) *
       omega (ψ 5 (σ 5 ⟨6, by decide⟩).1) (ψ 6 (σ 6 ⟨5, by decide⟩).1) *
       omega (ψ 1 (σ 1 ⟨5, by decide⟩).1) (ψ 5 (σ 5 ⟨1, by decide⟩).1) *
       omega (ψ 2 (σ 2 ⟨6, by decide⟩).1) (ψ 6 (σ 6 ⟨2, by decide⟩).1))) = rightHalf8C ψ c := by
  have hR : ∀ R : Half8Idx,
      let σ := wagnerSourceEquiv (zeroHalf8, R)
      ((ψ 1 (σ 1 ⟨0, by decide⟩).1 (invBit (c 0)) * ψ 2 (σ 2 ⟨3, by decide⟩).1 (c 1) *
        ψ 5 (σ 5 ⟨4, by decide⟩).1 (invBit (c 2)) * ψ 6 (σ 6 ⟨7, by decide⟩).1 (c 3)) *
       (omega (ψ 1 (σ 1 ⟨2, by decide⟩).1) (ψ 2 (σ 2 ⟨1, by decide⟩).1) *
        omega (ψ 5 (σ 5 ⟨6, by decide⟩).1) (ψ 6 (σ 6 ⟨5, by decide⟩).1) *
        omega (ψ 1 (σ 1 ⟨5, by decide⟩).1) (ψ 5 (σ 5 ⟨1, by decide⟩).1) *
        omega (ψ 2 (σ 2 ⟨6, by decide⟩).1) (ψ 6 (σ 6 ⟨2, by decide⟩).1))) =
      ∑ r : Fin 2 → Fin 2, sgn2C r *
        (omega (ψ 1 (wagnerNbr 1 (perm3Fun R.1.1 (wagnerNbrIdx 1 2))))
               (ψ 2 (wagnerNbr 2 (perm3Fun R.1.2 (wagnerNbrIdx 2 1)))) *
         ((ψ 1 (wagnerNbr 1 (perm3Fun R.1.1 (wagnerNbrIdx 1 0))) (invBit (c 0)) *
           ψ 1 (wagnerNbr 1 (perm3Fun R.1.1 (wagnerNbrIdx 1 5))) (r 0)) *
          (ψ 2 (wagnerNbr 2 (perm3Fun R.1.2 (wagnerNbrIdx 2 3))) (c 1) *
           ψ 2 (wagnerNbr 2 (perm3Fun R.1.2 (wagnerNbrIdx 2 6))) (r 1)))) *
        (omega (ψ 5 (wagnerNbr 5 (perm3Fun R.2.1 (wagnerNbrIdx 5 6))))
               (ψ 6 (wagnerNbr 6 (perm3Fun R.2.2 (wagnerNbrIdx 6 5)))) *
         ((ψ 5 (wagnerNbr 5 (perm3Fun R.2.1 (wagnerNbrIdx 5 1))) (invBit (r 0)) *
           ψ 5 (wagnerNbr 5 (perm3Fun R.2.1 (wagnerNbrIdx 5 4))) (invBit (c 2))) *
          (ψ 6 (wagnerNbr 6 (perm3Fun R.2.2 (wagnerNbrIdx 6 2))) (invBit (r 1)) *
           ψ 6 (wagnerNbr 6 (perm3Fun R.2.2 (wagnerNbrIdx 6 7))) (c 3)))) := by
    intro R
    let f : Fin 2 → Fin 2 → ℂ := fun i k => match i with
      | 0 => ψ 1 (wagnerNbr 1 (perm3Fun R.1.1 (wagnerNbrIdx 1 5))) k *
             ψ 5 (wagnerNbr 5 (perm3Fun R.2.1 (wagnerNbrIdx 5 1))) (invBit k)
      | 1 => ψ 2 (wagnerNbr 2 (perm3Fun R.1.2 (wagnerNbrIdx 2 6))) k *
             ψ 6 (wagnerNbr 6 (perm3Fun R.2.2 (wagnerNbrIdx 6 2))) (invBit k)
    have hf0 : omega (ψ 1 (wagnerNbr 1 (perm3Fun R.1.1 (wagnerNbrIdx 1 5))))
                     (ψ 5 (wagnerNbr 5 (perm3Fun R.2.1 (wagnerNbrIdx 5 1)))) = f 0 0 - f 0 1 :=
      omega_eq_sub_bit _ _
    have hf1 : omega (ψ 2 (wagnerNbr 2 (perm3Fun R.1.2 (wagnerNbrIdx 2 6))))
                     (ψ 6 (wagnerNbr 6 (perm3Fun R.2.2 (wagnerNbrIdx 6 2)))) = f 1 0 - f 1 1 :=
      omega_eq_sub_bit _ _
    have hsplit : (∏ i : Fin 2, (f i 0 - f i 1)) =
        ∑ r : Fin 2 → Fin 2, ∏ i : Fin 2, sgnBitC (r i) * f i (r i) := prod_fin2_sub 2 f
    dsimp only
    simp only [wagnerSourceEquiv_apply, pickVert8] at *
    rw [hf0, hf1, mul_assoc (omega _ _ * omega _ _), ← Fin.prod_univ_two (fun i => f i 0 - f i 1), hsplit, ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Fin.prod_univ_two, sgn2C, f]
    ring
  simp_rw [hR]
  rw [Finset.sum_comm]
  dsimp only [rightHalf8C]
  rw [← sum_bitFun_eq_sumBits 2]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_prod2 (sgn2C r)
    (fun R1 : Block2Idx =>
      omega (ψ 1 (wagnerNbr 1 (perm3Fun R1.1 (wagnerNbrIdx 1 2))))
            (ψ 2 (wagnerNbr 2 (perm3Fun R1.2 (wagnerNbrIdx 2 1)))) *
      ((ψ 1 (wagnerNbr 1 (perm3Fun R1.1 (wagnerNbrIdx 1 0))) (invBit (c 0)) *
        ψ 1 (wagnerNbr 1 (perm3Fun R1.1 (wagnerNbrIdx 1 5))) (r 0)) *
       (ψ 2 (wagnerNbr 2 (perm3Fun R1.2 (wagnerNbrIdx 2 3))) (c 1) *
        ψ 2 (wagnerNbr 2 (perm3Fun R1.2 (wagnerNbrIdx 2 6))) (r 1))))
    (fun R2 : Block2Idx =>
      omega (ψ 5 (wagnerNbr 5 (perm3Fun R2.1 (wagnerNbrIdx 5 6))))
            (ψ 6 (wagnerNbr 6 (perm3Fun R2.2 (wagnerNbrIdx 6 5)))) *
      ((ψ 5 (wagnerNbr 5 (perm3Fun R2.1 (wagnerNbrIdx 5 1))) (invBit (r 0)) *
        ψ 5 (wagnerNbr 5 (perm3Fun R2.1 (wagnerNbrIdx 5 4))) (invBit (c 2))) *
       (ψ 6 (wagnerNbr 6 (perm3Fun R2.2 (wagnerNbrIdx 6 2))) (invBit (r 1)) *
        ψ 6 (wagnerNbr 6 (perm3Fun R2.2 (wagnerNbrIdx 6 7))) (c 3)))),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [block2ValC]

theorem malkounNum_wagner_4block (ψ : Fin 8 → Fin 8 → Fin 2 → ℂ) :
    malkounNum wagnerGraph ψ = sumBits 4 fun c => sgn4C c * leftHalf8C ψ c * rightHalf8C ψ c := by
  unfold malkounNum
  rw [← Fintype.sum_equiv wagnerSourceEquiv
    (fun p => ∏ e : OriEdge wagnerGraph,
      omega (ψ e.1.1 ((wagnerSourceEquiv p) e.1.1 ⟨e.1.2, e.2.1⟩).1)
            (ψ e.1.2 ((wagnerSourceEquiv p) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
    (fun σ => ∏ e : OriEdge wagnerGraph,
      omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
    (fun _ => rfl)]
  have hterm : ∀ p : WagnerPermIdx,
      (∏ e : OriEdge wagnerGraph,
        omega (ψ e.1.1 ((wagnerSourceEquiv p) e.1.1 ⟨e.1.2, e.2.1⟩).1)
              (ψ e.1.2 ((wagnerSourceEquiv p) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)) =
      ∑ c : Fin 4 → Fin 2, sgn4C c *
        (let σL := wagnerSourceEquiv (p.1, zeroHalf8)
         (ψ 0 (σL 0 ⟨1, by decide⟩).1 (c 0) * ψ 3 (σL 3 ⟨2, by decide⟩).1 (invBit (c 1)) *
          ψ 4 (σL 4 ⟨5, by decide⟩).1 (c 2) * ψ 7 (σL 7 ⟨6, by decide⟩).1 (invBit (c 3))) *
         (omega (ψ 0 (σL 0 ⟨4, by decide⟩).1) (ψ 4 (σL 4 ⟨0, by decide⟩).1) *
          omega (ψ 3 (σL 3 ⟨7, by decide⟩).1) (ψ 7 (σL 7 ⟨3, by decide⟩).1) *
          omega (ψ 0 (σL 0 ⟨7, by decide⟩).1) (ψ 7 (σL 7 ⟨0, by decide⟩).1) *
          omega (ψ 3 (σL 3 ⟨4, by decide⟩).1) (ψ 4 (σL 4 ⟨3, by decide⟩).1))) *
        (let σR := wagnerSourceEquiv (zeroHalf8, p.2)
         (ψ 1 (σR 1 ⟨0, by decide⟩).1 (invBit (c 0)) * ψ 2 (σR 2 ⟨3, by decide⟩).1 (c 1) *
          ψ 5 (σR 5 ⟨4, by decide⟩).1 (invBit (c 2)) * ψ 6 (σR 6 ⟨7, by decide⟩).1 (c 3)) *
         (omega (ψ 1 (σR 1 ⟨2, by decide⟩).1) (ψ 2 (σR 2 ⟨1, by decide⟩).1) *
          omega (ψ 5 (σR 5 ⟨6, by decide⟩).1) (ψ 6 (σR 6 ⟨5, by decide⟩).1) *
          omega (ψ 1 (σR 1 ⟨5, by decide⟩).1) (ψ 5 (σR 5 ⟨1, by decide⟩).1) *
          omega (ψ 2 (σR 2 ⟨6, by decide⟩).1) (ψ 6 (σR 6 ⟨2, by decide⟩).1))) := by
    intro p
    let σ := wagnerSourceEquiv p
    rw [← Fintype.prod_equiv wagnerOriEquiv
      (fun x => omega (ψ (wagnerOriEquiv x).1.1 (σ (wagnerOriEquiv x).1.1 ⟨(wagnerOriEquiv x).1.2, (wagnerOriEquiv x).2.1⟩).1)
                      (ψ (wagnerOriEquiv x).1.2 (σ (wagnerOriEquiv x).1.2 ⟨(wagnerOriEquiv x).1.1, (wagnerOriEquiv x).2.1.symm⟩).1))
      (fun e => omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
      (fun _ => rfl)]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
    let fc : Fin 4 → Fin 2 → ℂ := fun i k => match i with
      | 0 => ψ 0 (σ 0 ⟨1, by decide⟩).1 k * ψ 1 (σ 1 ⟨0, by decide⟩).1 (invBit k)
      | 1 => ψ 2 (σ 2 ⟨3, by decide⟩).1 k * ψ 3 (σ 3 ⟨2, by decide⟩).1 (invBit k)
      | 2 => ψ 4 (σ 4 ⟨5, by decide⟩).1 k * ψ 5 (σ 5 ⟨4, by decide⟩).1 (invBit k)
      | 3 => ψ 6 (σ 6 ⟨7, by decide⟩).1 k * ψ 7 (σ 7 ⟨6, by decide⟩).1 (invBit k)
    have hcut : (∏ i : Fin 4,
        omega (ψ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.1 (σ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.1 ⟨(wagnerOriEquiv (.inr (.inr (.inr i)))).1.2, (wagnerOriEquiv (.inr (.inr (.inr i)))).2.1⟩).1)
              (ψ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.2 (σ (wagnerOriEquiv (.inr (.inr (.inr i)))).1.2 ⟨(wagnerOriEquiv (.inr (.inr (.inr i)))).1.1, (wagnerOriEquiv (.inr (.inr (.inr i)))).2.1.symm⟩).1)) =
        ∏ i : Fin 4, (fc i 0 - fc i 1) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i <;> rw [wagnerOri_term_inrrr] <;> exact omega_eq_sub_bit _ _
    simp_rw [wagnerOri_term_inl, wagnerOri_term_inrl, wagnerOri_term_inrrl]
    rw [hcut, prod_fin2_sub 4 fc]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Fin.prod_univ_four, sgn4C, fc]
    dsimp only [σ, zeroHalf8]
    simp_rw [wagnerSourceEquiv_apply']
    simp only [wagnerInternalEdges, wagnerIntraLeftEdges, wagnerIntraRightEdges,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pickVert8]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm, ← sum_bitFun_eq_sumBits 4]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_prod2 (sgn4C c)
    (fun L : Half8Idx =>
      let σL := wagnerSourceEquiv (L, zeroHalf8)
      (ψ 0 (σL 0 ⟨1, by decide⟩).1 (c 0) * ψ 3 (σL 3 ⟨2, by decide⟩).1 (invBit (c 1)) *
       ψ 4 (σL 4 ⟨5, by decide⟩).1 (c 2) * ψ 7 (σL 7 ⟨6, by decide⟩).1 (invBit (c 3))) *
      (omega (ψ 0 (σL 0 ⟨4, by decide⟩).1) (ψ 4 (σL 4 ⟨0, by decide⟩).1) *
       omega (ψ 3 (σL 3 ⟨7, by decide⟩).1) (ψ 7 (σL 7 ⟨3, by decide⟩).1) *
       omega (ψ 0 (σL 0 ⟨7, by decide⟩).1) (ψ 7 (σL 7 ⟨0, by decide⟩).1) *
       omega (ψ 3 (σL 3 ⟨4, by decide⟩).1) (ψ 4 (σL 4 ⟨3, by decide⟩).1)))
    (fun R : Half8Idx =>
      let σR := wagnerSourceEquiv (zeroHalf8, R)
      (ψ 1 (σR 1 ⟨0, by decide⟩).1 (invBit (c 0)) * ψ 2 (σR 2 ⟨3, by decide⟩).1 (c 1) *
       ψ 5 (σR 5 ⟨4, by decide⟩).1 (invBit (c 2)) * ψ 6 (σR 6 ⟨7, by decide⟩).1 (c 3)) *
      (omega (ψ 1 (σR 1 ⟨2, by decide⟩).1) (ψ 2 (σR 2 ⟨1, by decide⟩).1) *
       omega (ψ 5 (σR 5 ⟨6, by decide⟩).1) (ψ 6 (σR 6 ⟨5, by decide⟩).1) *
       omega (ψ 1 (σR 1 ⟨5, by decide⟩).1) (ψ 5 (σR 5 ⟨1, by decide⟩).1) *
       omega (ψ 2 (σR 2 ⟨6, by decide⟩).1) (ψ 6 (σR 6 ⟨2, by decide⟩).1))),
    wagner_left_block_eq ψ c, wagner_right_block_eq ψ c]

end WagnerDecomposition

/-! ## Part 3: Gaussian-Integer & Closed Interval Verification of 4-Block Evaluators -/

section WagnerEvaluators

private def sgnBitGI (b : Fin 2) : GI := if b = 0 then 1 else GI.ofInt (-1)
private def sgn2GI (b : Fin 2 → Fin 2) : GI := sgnBitGI (b 0) * sgnBitGI (b 1)
private def sgn4GI (b : Fin 4 → Fin 2) : GI := sgnBitGI (b 0) * sgnBitGI (b 1) * sgnBitGI (b 2) * sgnBitGI (b 3)
private def sgnIntBit (b : Fin 2) : ℤ := if b = 0 then 1 else -1
private def sgnInt2 (b : Fin 2 → Fin 2) : ℤ := sgnIntBit (b 0) * sgnIntBit (b 1)
private def sgnInt4 (b : Fin 4 → Fin 2) : ℤ := sgnIntBit (b 0) * sgnIntBit (b 1) * sgnIntBit (b 2) * sgnIntBit (b 3)

private lemma toC_sgnBitGI (b : Fin 2) : GI.toC (sgnBitGI b) = sgnBitC b := by
  fin_cases b <;> simp [sgnBitGI, sgnBitC, GI.toC_ofInt]

private lemma toC_sgn2GI (b : Fin 2 → Fin 2) : GI.toC (sgn2GI b) = sgn2C b := by
  simp only [sgn2GI, sgn2C, GI.toC_mul, toC_sgnBitGI]

private lemma toC_sgn4GI (b : Fin 4 → Fin 2) : GI.toC (sgn4GI b) = sgn4C b := by
  rw [sgn4GI, sgn4C, Fin.prod_univ_four]
  simp only [GI.toC_mul, toC_sgnBitGI]

private lemma sgnInt2_eq (b : Fin 2 → Fin 2) : ((sgnInt2 b : ℤ) : ℂ) = sgn2C b := by
  rcases fin2_cases (b 0) with h0 | h0 <;> rcases fin2_cases (b 1) with h1 | h1 <;>
    simp [sgnInt2, sgn2C, sgnIntBit, sgnBitC, h0, h1]

private lemma sgnInt4_eq (b : Fin 4 → Fin 2) : ((sgnInt4 b : ℤ) : ℂ) = sgn4C b := by
  rw [sgn4C, Fin.prod_univ_four]
  simp only [sgnInt4, Int.cast_mul]
  have hcast : ∀ x : Fin 2, ((sgnIntBit x : ℤ) : ℂ) = sgnBitC x := fun x => by fin_cases x <;> simp [sgnIntBit, sgnBitC]
  rw [hcast, hcast, hcast, hcast]

def sumFin6 {R : Type*} [Add R] (f : Fin 6 → R) : R :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5

private lemma sumFin6_eq_sum (f : Fin 6 → ℂ) : (∑ i : Fin 6, f i) = sumFin6 f := by
  rw [Fin.sum_univ_six, sumFin6]

private lemma toC_sumFin6 (f : Fin 6 → GI) : GI.toC (sumFin6 f) = sumFin6 (fun i => GI.toC (f i)) := by
  simp only [sumFin6, GI.toC_add]

private lemma sumFin6_mem (f : Fin 6 → CIntIv) (fc : Fin 6 → ℂ) (hf : ∀ i, (f i).Mem (fc i)) :
    (sumFin6 f).Mem (sumFin6 fc) := by
  simp only [sumFin6]
  exact CIntIv.add_mem (CIntIv.add_mem (CIntIv.add_mem (CIntIv.add_mem (CIntIv.add_mem (hf 0) (hf 1)) (hf 2)) (hf 3)) (hf 4)) (hf 5)

private lemma toC_sumBits : ∀ (m : ℕ) (f : (Fin m → Fin 2) → GI),
    GI.toC (sumBits m f) = sumBits m (fun b => GI.toC (f b))
  | 0, _ => rfl
  | m + 1, f => by simp only [sumBits, GI.toC_add, toC_sumBits m]

private lemma sumBits_mem : ∀ (m : ℕ) (f : (Fin m → Fin 2) → CIntIv) (fc : (Fin m → Fin 2) → ℂ),
    (∀ b, (f b).Mem (fc b)) → (sumBits m f).Mem (sumBits m fc)
  | 0, _, _, h => h Fin.elim0
  | m + 1, _f, _fc, h => CIntIv.add_mem (sumBits_mem m _ _ fun _b => h _) (sumBits_mem m _ _ fun _b => h _)

def block2ValGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI)
    (u v p0 p1 p2 p3 : Fin 8) (b0 b1 b2 b3 : Fin 2) : GI :=
  sumFin6 fun i => sumFin6 fun j =>
    omegaGI (ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u v))))
            (ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v u)))) *
    ((ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u p0))) b0 *
      ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u p1))) b1) *
     (ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v p2))) b2 *
      ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v p3))) b3))

private lemma toC_block2ValGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) (u v p0 p1 p2 p3 : Fin 8) (b0 b1 b2 b3 : Fin 2) :
    GI.toC (block2ValGI ψ u v p0 p1 p2 p3 b0 b1 b2 b3) =
      block2ValC (fun x y k => GI.toC (ψ x y k)) u v p0 p1 p2 p3 b0 b1 b2 b3 := by
  rw [block2ValGI, block2ValC, toC_sumFin6, sumFin6_eq_sum]
  congr 1; ext i
  rw [toC_sumFin6, sumFin6_eq_sum]
  congr 1; ext j
  simp only [GI.toC_mul, toC_omegaGI]

def leftHalf8GI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) (c : Fin 4 → Fin 2) : GI :=
  sumBits 2 fun b =>
    sgn2GI b *
      block2ValGI ψ 0 4 1 7 3 5 (c 0) (b 0) (invBit (b 1)) (c 2) *
      block2ValGI ψ 3 7 2 4 0 6 (invBit (c 1)) (b 1) (invBit (b 0)) (invBit (c 3))

def rightHalf8GI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) (c : Fin 4 → Fin 2) : GI :=
  sumBits 2 fun r =>
    sgn2GI r *
      block2ValGI ψ 1 2 0 5 3 6 (invBit (c 0)) (r 0) (c 1) (r 1) *
      block2ValGI ψ 5 6 1 4 2 7 (invBit (r 0)) (invBit (c 2)) (invBit (r 1)) (c 3)

def wagnerNumGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) : GI :=
  sumBits 4 fun c => sgn4GI c * leftHalf8GI ψ c * rightHalf8GI ψ c

def prod4GI (g : Fin 4 → GI) : GI := g 0 * g 1 * g 2 * g 3
def prod2GI' (g : Fin 2 → GI) : GI := g 0 * g 1

def wagnerDenGI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) : GI :=
  prod4GI (fun i => omegaGI (ψ (wagnerInternalEdges i).1 (wagnerInternalEdges i).2) (ψ (wagnerInternalEdges i).2 (wagnerInternalEdges i).1)) *
  prod2GI' (fun i => omegaGI (ψ (wagnerIntraLeftEdges i).1 (wagnerIntraLeftEdges i).2) (ψ (wagnerIntraLeftEdges i).2 (wagnerIntraLeftEdges i).1)) *
  prod2GI' (fun i => omegaGI (ψ (wagnerIntraRightEdges i).1 (wagnerIntraRightEdges i).2) (ψ (wagnerIntraRightEdges i).2 (wagnerIntraRightEdges i).1)) *
  prod4GI (fun i => omegaGI (ψ (wagnerCutEdges i).1 (wagnerCutEdges i).2) (ψ (wagnerCutEdges i).2 (wagnerCutEdges i).1))

private lemma toC_prod4GI (g : Fin 4 → GI) : GI.toC (prod4GI g) = ∏ i : Fin 4, GI.toC (g i) := by
  rw [Fin.prod_univ_four, prod4GI]; simp only [GI.toC_mul]

private lemma toC_prod2GI' (g : Fin 2 → GI) : GI.toC (prod2GI' g) = ∏ i : Fin 2, GI.toC (g i) := by
  rw [Fin.prod_univ_two, prod2GI']; simp only [GI.toC_mul]

private lemma sumBits_congr {R : Type*} [Add R] :
    ∀ (m : ℕ) {f g : (Fin m → Fin 2) → R}, (∀ b, f b = g b) → sumBits m f = sumBits m g
  | 0, _, _, h => h Fin.elim0
  | m + 1, _, _, h => by simp only [sumBits]; rw [sumBits_congr m (fun f => h (Fin.cons 0 f)), sumBits_congr m (fun f => h (Fin.cons 1 f))]

private lemma toC_leftHalf8GI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) (c : Fin 4 → Fin 2) :
    GI.toC (leftHalf8GI ψ c) = leftHalf8C (fun u v k => GI.toC (ψ u v k)) c := by
  rw [leftHalf8GI, leftHalf8C, toC_sumBits]
  refine sumBits_congr 2 fun b => ?_
  simp only [GI.toC_mul, toC_sgn2GI, toC_block2ValGI]

private lemma toC_rightHalf8GI (ψ : Fin 8 → Fin 8 → Fin 2 → GI) (c : Fin 4 → Fin 2) :
    GI.toC (rightHalf8GI ψ c) = rightHalf8C (fun u v k => GI.toC (ψ u v k)) c := by
  rw [rightHalf8GI, rightHalf8C, toC_sumBits]
  refine sumBits_congr 2 fun r => ?_
  simp only [GI.toC_mul, toC_sgn2GI, toC_block2ValGI]

theorem malkounNum_wagner_giToC (ψ : Fin 8 → Fin 8 → Fin 2 → GI) :
    GI.toC (wagnerNumGI ψ) = malkounNum wagnerGraph (fun u v k => GI.toC (ψ u v k)) := by
  rw [malkounNum_wagner_4block, wagnerNumGI, toC_sumBits]
  refine sumBits_congr 4 fun c => ?_
  rw [GI.toC_mul, GI.toC_mul, toC_sgn4GI, toC_leftHalf8GI, toC_rightHalf8GI]

theorem malkounDen_wagner_giToC (ψ : Fin 8 → Fin 8 → Fin 2 → GI) :
    GI.toC (wagnerDenGI ψ) = malkounDen wagnerGraph (fun u v k => GI.toC (ψ u v k)) := by
  let ψC : Fin 8 → Fin 8 → Fin 2 → ℂ := fun u v k => GI.toC (ψ u v k)
  change GI.toC (wagnerDenGI ψ) = malkounDen wagnerGraph ψC
  unfold malkounDen wagnerDenGI
  rw [← Fintype.prod_equiv wagnerOriEquiv
    (fun x => omega (ψC (wagnerOriEquiv x).1.1 (wagnerOriEquiv x).1.2)
                    (ψC (wagnerOriEquiv x).1.2 (wagnerOriEquiv x).1.1))
    (fun e => omega (ψC e.1.1 e.1.2) (ψC e.1.2 e.1.1)) (fun _ => rfl)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [← mul_assoc]
  simp_rw [wagnerOri_den_inl, wagnerOri_den_inrl, wagnerOri_den_inrrl, wagnerOri_den_inrrr]
  simp only [ψC, GI.toC_mul, toC_prod4GI, toC_prod2GI', toC_omegaGI]

def block2ValIv (ψ : Fin 8 → Fin 8 → Fin 2 → CIntIv)
    (u v p0 p1 p2 p3 : Fin 8) (b0 b1 b2 b3 : Fin 2) : CIntIv :=
  sumFin6 fun i => sumFin6 fun j =>
    omegaIv (ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u v))))
            (ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v u)))) *
    ((ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u p0))) b0 *
      ψ u (wagnerNbr u (perm3Fun i (wagnerNbrIdx u p1))) b1) *
     (ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v p2))) b2 *
      ψ v (wagnerNbr v (perm3Fun j (wagnerNbrIdx v p3))) b3))

private lemma block2ValIv_mem (ψIv : Fin 8 → Fin 8 → Fin 2 → CIntIv) (ψC : Fin 8 → Fin 8 → Fin 2 → ℂ)
    (hψ : ∀ u v, wagnerGraph.Adj u v → ∀ k, (ψIv u v k).Mem (ψC u v k))
    (u v p0 p1 p2 p3 : Fin 8) (b0 b1 b2 b3 : Fin 2) :
    (block2ValIv ψIv u v p0 p1 p2 p3 b0 b1 b2 b3).Mem (block2ValC ψC u v p0 p1 p2 p3 b0 b1 b2 b3) := by
  rw [block2ValIv, block2ValC, sumFin6_eq_sum]
  refine sumFin6_mem _ _ fun i => ?_
  rw [sumFin6_eq_sum]
  refine sumFin6_mem _ _ fun j => ?_
  exact CIntIv.mul_mem
    (omegaIv_mem (hψ u _ (wagnerNbr_adj u _)) (hψ v _ (wagnerNbr_adj v _)))
    (CIntIv.mul_mem
      (CIntIv.mul_mem (hψ u _ (wagnerNbr_adj u _) b0) (hψ u _ (wagnerNbr_adj u _) b1))
      (CIntIv.mul_mem (hψ v _ (wagnerNbr_adj v _) b2) (hψ v _ (wagnerNbr_adj v _) b3)))

def wagnerBlockTab := Fin 2 → Fin 2 → Fin 2 → Fin 2 → CIntIv

def leftHalf8TabsIv (t0 t1 : wagnerBlockTab) (c : Fin 4 → Fin 2) : CIntIv :=
  sumBits 2 fun b =>
    (t0 (c 0) (b 0) (invBit (b 1)) (c 2) *
     t1 (invBit (c 1)) (b 1) (invBit (b 0)) (invBit (c 3))).scaleInt (sgnInt2 b)

def rightHalf8TabsIv (t2 t3 : wagnerBlockTab) (c : Fin 4 → Fin 2) : CIntIv :=
  sumBits 2 fun r =>
    (t2 (invBit (c 0)) (r 0) (c 1) (r 1) *
     t3 (invBit (r 0)) (invBit (c 2)) (invBit (r 1)) (c 3)).scaleInt (sgnInt2 r)

def wagnerNumTabsIv (lTab rTab : (Fin 4 → Fin 2) → CIntIv) : CIntIv :=
  sumBits 4 fun c => (lTab c * rTab c).scaleInt (sgnInt4 c)

def wagnerNumIv (ψ : Fin 8 → Fin 8 → Fin 2 → CIntIv) : CIntIv :=
  let t0 : wagnerBlockTab := fun a b c d => block2ValIv ψ 0 4 1 7 3 5 a b c d
  let t1 : wagnerBlockTab := fun a b c d => block2ValIv ψ 3 7 2 4 0 6 a b c d
  let t2 : wagnerBlockTab := fun a b c d => block2ValIv ψ 1 2 0 5 3 6 a b c d
  let t3 : wagnerBlockTab := fun a b c d => block2ValIv ψ 5 6 1 4 2 7 a b c d
  wagnerNumTabsIv (leftHalf8TabsIv t0 t1) (rightHalf8TabsIv t2 t3)

theorem wagnerNumIv_mem (ψIv : Fin 8 → Fin 8 → Fin 2 → CIntIv) (ψC : Fin 8 → Fin 8 → Fin 2 → ℂ)
    (hψ : ∀ u v, wagnerGraph.Adj u v → ∀ k, (ψIv u v k).Mem (ψC u v k)) :
    (wagnerNumIv ψIv).Mem (malkounNum wagnerGraph ψC) := by
  rw [malkounNum_wagner_4block]
  dsimp only [wagnerNumIv, wagnerNumTabsIv, leftHalf8TabsIv, rightHalf8TabsIv, leftHalf8C, rightHalf8C]
  refine sumBits_mem 4 _ _ fun c => ?_
  rw [← sgnInt4_eq c, mul_assoc]
  refine CIntIv.scaleInt_mem (CIntIv.mul_mem ?_ ?_)
  · refine sumBits_mem 2 _ _ fun b => ?_
    rw [← sgnInt2_eq b, mul_assoc]
    exact CIntIv.scaleInt_mem (CIntIv.mul_mem
      (block2ValIv_mem ψIv ψC hψ 0 4 1 7 3 5 _ _ _ _)
      (block2ValIv_mem ψIv ψC hψ 3 7 2 4 0 6 _ _ _ _))
  · refine sumBits_mem 2 _ _ fun r => ?_
    rw [← sgnInt2_eq r, mul_assoc]
    exact CIntIv.scaleInt_mem (CIntIv.mul_mem
      (block2ValIv_mem ψIv ψC hψ 1 2 0 5 3 6 _ _ _ _)
      (block2ValIv_mem ψIv ψC hψ 5 6 1 4 2 7 _ _ _ _))

def prod4Iv (g : Fin 4 → CIntIv) : CIntIv := g 0 * g 1 * g 2 * g 3

private lemma prod4Iv_mem (g : Fin 4 → CIntIv) (gc : Fin 4 → ℂ) (hg : ∀ i, (g i).Mem (gc i)) :
    (prod4Iv g).Mem (∏ i : Fin 4, gc i) := by
  rw [Fin.prod_univ_four]
  exact CIntIv.mul_mem (CIntIv.mul_mem (CIntIv.mul_mem (hg 0) (hg 1)) (hg 2)) (hg 3)

def wagnerDenIv (ψ : Fin 8 → Fin 8 → Fin 2 → CIntIv) : CIntIv :=
  prod4Iv (fun i => omegaIv (ψ (wagnerInternalEdges i).1 (wagnerInternalEdges i).2) (ψ (wagnerInternalEdges i).2 (wagnerInternalEdges i).1)) *
  prod2Iv (fun i => omegaIv (ψ (wagnerIntraLeftEdges i).1 (wagnerIntraLeftEdges i).2) (ψ (wagnerIntraLeftEdges i).2 (wagnerIntraLeftEdges i).1)) *
  prod2Iv (fun i => omegaIv (ψ (wagnerIntraRightEdges i).1 (wagnerIntraRightEdges i).2) (ψ (wagnerIntraRightEdges i).2 (wagnerIntraRightEdges i).1)) *
  prod4Iv (fun i => omegaIv (ψ (wagnerCutEdges i).1 (wagnerCutEdges i).2) (ψ (wagnerCutEdges i).2 (wagnerCutEdges i).1))

theorem wagnerDenIv_mem (ψIv : Fin 8 → Fin 8 → Fin 2 → CIntIv) (ψC : Fin 8 → Fin 8 → Fin 2 → ℂ)
    (hψ : ∀ u v, wagnerGraph.Adj u v → ∀ k, (ψIv u v k).Mem (ψC u v k)) :
    (wagnerDenIv ψIv).Mem (malkounDen wagnerGraph ψC) := by
  unfold malkounDen wagnerDenIv
  rw [← Fintype.prod_equiv wagnerOriEquiv
    (fun x => omega (ψC (wagnerOriEquiv x).1.1 (wagnerOriEquiv x).1.2)
                    (ψC (wagnerOriEquiv x).1.2 (wagnerOriEquiv x).1.1))
    (fun e => omega (ψC e.1.1 e.1.2) (ψC e.1.2 e.1.1)) (fun _ => rfl)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [← mul_assoc]
  simp_rw [wagnerOri_den_inl, wagnerOri_den_inrl, wagnerOri_den_inrrl, wagnerOri_den_inrrr]
  have h1 := prod4Iv_mem
    (fun i => omegaIv (ψIv (wagnerInternalEdges i).1 (wagnerInternalEdges i).2) (ψIv (wagnerInternalEdges i).2 (wagnerInternalEdges i).1))
    (fun i => omega (ψC (wagnerInternalEdges i).1 (wagnerInternalEdges i).2) (ψC (wagnerInternalEdges i).2 (wagnerInternalEdges i).1))
    fun i => omegaIv_mem (hψ _ _ (wagnerInternalEdges_ok i).1) (hψ _ _ (wagnerInternalEdges_ok i).1.symm)
  have h2 := prod2Iv_mem
    (fun i => omegaIv (ψIv (wagnerIntraLeftEdges i).1 (wagnerIntraLeftEdges i).2) (ψIv (wagnerIntraLeftEdges i).2 (wagnerIntraLeftEdges i).1))
    (fun i => omega (ψC (wagnerIntraLeftEdges i).1 (wagnerIntraLeftEdges i).2) (ψC (wagnerIntraLeftEdges i).2 (wagnerIntraLeftEdges i).1))
    fun i => omegaIv_mem (hψ _ _ (wagnerIntraLeftEdges_ok i).1) (hψ _ _ (wagnerIntraLeftEdges_ok i).1.symm)
  have h3 := prod2Iv_mem
    (fun i => omegaIv (ψIv (wagnerIntraRightEdges i).1 (wagnerIntraRightEdges i).2) (ψIv (wagnerIntraRightEdges i).2 (wagnerIntraRightEdges i).1))
    (fun i => omega (ψC (wagnerIntraRightEdges i).1 (wagnerIntraRightEdges i).2) (ψC (wagnerIntraRightEdges i).2 (wagnerIntraRightEdges i).1))
    fun i => omegaIv_mem (hψ _ _ (wagnerIntraRightEdges_ok i).1) (hψ _ _ (wagnerIntraRightEdges_ok i).1.symm)
  have h4 := prod4Iv_mem
    (fun i => omegaIv (ψIv (wagnerCutEdges i).1 (wagnerCutEdges i).2) (ψIv (wagnerCutEdges i).2 (wagnerCutEdges i).1))
    (fun i => omega (ψC (wagnerCutEdges i).1 (wagnerCutEdges i).2) (ψC (wagnerCutEdges i).2 (wagnerCutEdges i).1))
    fun i => omegaIv_mem (hψ _ _ (wagnerCutEdges_ok i).1) (hψ _ _ (wagnerCutEdges_ok i).1.symm)
  exact CIntIv.mul_mem (CIntIv.mul_mem (CIntIv.mul_mem h1 h2) h3) h4

end WagnerEvaluators

/-! ## Part 4: Concrete Witness for $M_8$, Collinear $t = 0$, $S = 10^6$ Certificates, and IVT -/

section WitnessAndDisproofs

def wagnerPtsX : Fin 8 → ℤ
  | 0 => 183
  | 1 => 414
  | 2 => -1609
  | 3 => 134
  | 4 => 174
  | 5 => 3967
  | 6 => 1
  | 7 => 182

def wagnerPtsY : Fin 8 → ℤ
  | 0 => -1727
  | 1 => -1680
  | 2 => 3064
  | 3 => -1776
  | 4 => -1744
  | 5 => 1
  | 6 => -1369
  | 7 => -1726

lemma wagnerPtsX_inj : Function.Injective wagnerPtsX := by
  intro a b h; fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)

def wagnerScale : ℤ := 1000000

def distWagnerLo : Fin 8 → Fin 8 → ℤ
  | 0, 1 => 235732899
  | 0, 4 => 19235384
  | 0, 7 => 1414213
  | 1, 0 => 235732899
  | 1, 2 => 5157331189
  | 1, 5 => 3930594102
  | 2, 1 => 5157331189
  | 2, 3 => 5144283137
  | 2, 6 => 4716310952
  | 3, 2 => 5144283137
  | 3, 4 => 51224993
  | 3, 7 => 69310893
  | 4, 0 => 19235384
  | 4, 3 => 51224993
  | 4, 5 => 4175149578
  | 5, 1 => 3930594102
  | 5, 4 => 4175149578
  | 5, 6 => 4195957101
  | 6, 2 => 4716310952
  | 6, 5 => 4195957101
  | 6, 7 => 400262413
  | 7, 0 => 1414213
  | 7, 3 => 69310893
  | 7, 6 => 400262413
  | _, _ => 0

theorem distWagnerLo_ok : ∀ u v : Fin 8, wagnerGraph.Adj u v →
    let dx := wagnerPtsX v - wagnerPtsX u
    let dy := wagnerPtsY v - wagnerPtsY u
    let lo := distWagnerLo u v
    0 ≤ lo ∧ lo * lo ≤ wagnerScale * wagnerScale * (dx * dx + dy * dy) ∧
      wagnerScale * wagnerScale * (dx * dx + dy * dy) ≤ (lo + 1) * (lo + 1) := by
  decide

def spinorsWagnerColGI (u v : Fin 8) : Fin 2 → GI :=
  spinorFromInts ((wagnerPtsX v - wagnerPtsX u).natAbs : ℤ) (wagnerPtsX v - wagnerPtsX u) 0

theorem spinorsWagnerColGI_ok : ∀ u v : Fin 8, wagnerGraph.Adj u v →
    let dx := wagnerPtsX v - wagnerPtsX u
    let r : ℤ := (dx.natAbs : ℤ)
    let g := scaleFromInts r dx 0
    g ≠ 0 ∧ 0 ≤ r ∧ r * r = dx * dx ∧
    r = g * (spinorsWagnerColGI u v 0).re ∧ (spinorsWagnerColGI u v 0).im = 0 ∧
    dx = g * (spinorsWagnerColGI u v 1).re ∧ (0 : ℤ) = g * (spinorsWagnerColGI u v 1).im := by
  decide

theorem cert_wagner_col_num : wagnerNumGI spinorsWagnerColGI = GI.ofInt 9437184 := by decide
theorem cert_wagner_col_den : wagnerDenGI spinorsWagnerColGI = GI.ofInt 4096 := by decide

def spinorsWagnerIv (u v : Fin 8) : Fin 2 → CIntIv
  | 0 => ⟨⟨distWagnerLo u v, distWagnerLo u v + 1⟩, IntIv.zero⟩
  | 1 => ⟨IntIv.ofInt (wagnerScale * (wagnerPtsX v - wagnerPtsX u)), IntIv.ofInt (wagnerScale * (wagnerPtsY v - wagnerPtsY u))⟩

def wagnerB0Val : Fin 2 → Fin 2 → Fin 2 → Fin 2 → CIntIv
  | 0, 0, 0, 0 => ⟨⟨250269017834974322745568703043156436363200000000, 250269650167324647470961818297526024730304000000⟩, ⟨207146769337839379397166607120014430831088000000, 207147369364350813583380866582898567861600000000⟩⟩
  | 0, 0, 0, 1 => ⟨⟨-51297465116503185905229785198634436000000000000, -51296669115639008075837499441956992000000000000⟩, ⟨-265389728719089338027121735824652316000000000000, -265388897250526263328588743844174200000000000000⟩⟩
  | 0, 0, 1, 0 => ⟨⟨-51297465116503185905229785198634436000000000000, -51296669115639008075837499441956992000000000000⟩, ⟨-265389728719089338027121735824652316000000000000, -265388897250526263328588743844174200000000000000⟩⟩
  | 0, 0, 1, 1 => ⟨⟨544725691495949011260837467136000000000000000000, 544726351555226585869561273480000000000000000000⟩, ⟨-791065929146941043274240437984000000000000000000, -791065201586334003382756529104000000000000000000⟩⟩
  | 0, 1, 0, 0 => ⟨⟨36897742966365972998847789331870918000000000000, 36898256081023497754982432102116480000000000000⟩, ⟨23361951971639876652307346319614526000000000000, 23362491973656022797285738869633064000000000000⟩⟩
  | 0, 1, 0, 1 => ⟨⟨8323646282532277504642857645000000000000000000, 8324238784663507556856004397000000000000000000⟩, ⟨36156856336234560374043612821000000000000000000, 36157467887307493283420769109000000000000000000⟩⟩
  | 0, 1, 1, 0 => ⟨⟨8323646282532277504642857645000000000000000000, 8324238784663507556856004397000000000000000000⟩, ⟨36156856336234560374043612821000000000000000000, 36157467887307493283420769109000000000000000000⟩⟩
  | 0, 1, 1, 1 => ⟨⟨-22968712427172409747260000000000000000000000000, -22968166869611390822876000000000000000000000000⟩, ⟨37144164889346231314336000000000000000000000000, 37144678807533432019744000000000000000000000000⟩⟩
  | 1, 0, 0, 0 => ⟨⟨36897742966365972998847789331870918000000000000, 36898256081023497754982432102116480000000000000⟩, ⟨23361951971639876652307346319614526000000000000, 23362491973656022797285738869633064000000000000⟩⟩
  | 1, 0, 0, 1 => ⟨⟨8323646282532277504642857645000000000000000000, 8324238784663507556856004397000000000000000000⟩, ⟨36156856336234560374043612821000000000000000000, 36157467887307493283420769109000000000000000000⟩⟩
  | 1, 0, 1, 0 => ⟨⟨8323646282532277504642857645000000000000000000, 8324238784663507556856004397000000000000000000⟩, ⟨36156856336234560374043612821000000000000000000, 36157467887307493283420769109000000000000000000⟩⟩
  | 1, 0, 1, 1 => ⟨⟨-22968712427172409747260000000000000000000000000, -22968166869611390822876000000000000000000000000⟩, ⟨37144164889346231314336000000000000000000000000, 37144678807533432019744000000000000000000000000⟩⟩
  | 1, 1, 0, 0 => ⟨⟨-835790874079331377928036146368000000000000000000, -835790606278525575066745542184000000000000000000⟩, ⟨-473249631532164270616413447808000000000000000000, -473249354224837985637353628024000000000000000000⟩⟩
  | 1, 1, 0, 1 => ⟨⟨-69909960431788040876688000000000000000000000000, -69909696825137960387476000000000000000000000000⟩, ⟨-261104488375037939807112000000000000000000000000, -261104229997153273740652000000000000000000000000⟩⟩
  | 1, 1, 1, 0 => ⟨⟨-69909960431788040876688000000000000000000000000, -69909696825137960387476000000000000000000000000⟩, ⟨-261104488375037939807112000000000000000000000000, -261104229997153273740652000000000000000000000000⟩⟩
  | 1, 1, 1, 1 => ⟨⟨-134500154200620016000000000000000000000000000000, -134499910579169312000000000000000000000000000000⟩, ⟨295726811145773920000000000000000000000000000000, 295727024178896816000000000000000000000000000000⟩⟩

def wagnerB1Val : Fin 2 → Fin 2 → Fin 2 → Fin 2 → CIntIv
  | 0, 0, 0, 0 => ⟨⟨-13519498811542013010298512929164326916747260000000, -13519482721060420554482432675002391409974004000000⟩, ⟨-24279546223730409939557695303730908755054504000000, -24279530354424607502141802989682529179473052000000⟩⟩
  | 0, 0, 0, 1 => ⟨⟨207918360593462363321219736304363694000000000000, 207933142879169456662367089303983136000000000000⟩, ⟨10104785048450117834146247340316161954000000000000, 10104799005282492704435527277811839928000000000000⟩⟩
  | 0, 0, 1, 0 => ⟨⟨207918360593462363321219736304363694000000000000, 207933142879169456662367089303983136000000000000⟩, ⟨10104785048450117834146247340316161954000000000000, 10104799005282492704435527277811839928000000000000⟩⟩
  | 0, 0, 1, 1 => ⟨⟨15447874627274344668801582244000000000000000000000, 15447880493554019343847164496168000000000000000000⟩, ⟨-26597645768755523337985144491672000000000000000000, -26597639284053540731913204634048000000000000000000⟩⟩
  | 0, 1, 0, 0 => ⟨⟨16502322968574366371200114001936126976000000000000, 16502343638499368112348049562470383398000000000000⟩, ⟨-21176351362374828233319704029486125940000000000000, -21176329279489618484388141202303089060000000000000⟩⟩
  | 0, 1, 0, 1 => ⟨⟨-8379470546121277817840063957696000000000000000000, -8379454213324244350593558783435000000000000000000⟩, ⟨3670612157431860143705430921356000000000000000000, 3670628230826669685189990027887000000000000000000⟩⟩
  | 0, 1, 1, 0 => ⟨⟨-8379470546121277817840063957696000000000000000000, -8379454213324244350593558783435000000000000000000⟩, ⟨3670612157431860143705430921356000000000000000000, 3670628230826669685189990027887000000000000000000⟩⟩
  | 0, 1, 1, 1 => ⟨⟨26754468717268455798627952000000000000000000000000, 26754474323666191596995484000000000000000000000000⟩, ⟨2227709077538601354762004000000000000000000000000, 2227715312796059237554736000000000000000000000000⟩⟩
  | 1, 0, 0, 0 => ⟨⟨16502322968574366371200114001936126976000000000000, 16502343638499368112348049562470383398000000000000⟩, ⟨-21176351362374828233319704029486125940000000000000, -21176329279489618484388141202303089060000000000000⟩⟩
  | 1, 0, 0, 1 => ⟨⟨-8379470546121277817840063957696000000000000000000, -8379454213324244350593558783435000000000000000000⟩, ⟨3670612157431860143705430921356000000000000000000, 3670628230826669685189990027887000000000000000000⟩⟩
  | 1, 0, 1, 0 => ⟨⟨-8379470546121277817840063957696000000000000000000, -8379454213324244350593558783435000000000000000000⟩, ⟨3670612157431860143705430921356000000000000000000, 3670628230826669685189990027887000000000000000000⟩⟩
  | 1, 0, 1, 1 => ⟨⟨26754468717268455798627952000000000000000000000000, 26754474323666191596995484000000000000000000000000⟩, ⟨2227709077538601354762004000000000000000000000000, 2227715312796059237554736000000000000000000000000⟩⟩
  | 1, 1, 0, 0 => ⟨⟨30024465165130097668601650881272000000000000000000, 30024487702649239363211282188024000000000000000000⟩, ⟨6678484090047793729669372755712000000000000000000, 6678501340757498734112283787464000000000000000000⟩⟩
  | 1, 1, 0, 1 => ⟨⟨-7286578650303064213832468000000000000000000000000, -7286563950966958893323680000000000000000000000000⟩, ⟨-7004002004738727349255616000000000000000000000000, -7003986392105791265826468000000000000000000000000⟩⟩
  | 1, 1, 1, 0 => ⟨⟨-7286578650303064213832468000000000000000000000000, -7286563950966958893323680000000000000000000000000⟩, ⟨-7004002004738727349255616000000000000000000000000, -7003986392105791265826468000000000000000000000000⟩⟩
  | 1, 1, 1, 1 => ⟨⟨8680361189343385312000000000000000000000000000000, 8680367668929681440000000000000000000000000000000⟩, ⟨26399314380351655264000000000000000000000000000000, 26399320180965099584000000000000000000000000000000⟩⟩

def wagnerB2Val : Fin 2 → Fin 2 → Fin 2 → Fin 2 → CIntIv
  | 0, 0, 0, 0 => ⟨⟨11054859733808029448265467869150485431860259581988640000000, 11054859802555109588594815174126074043683478840093896000000⟩, ⟨-28333505219574239282002552616183978909578440816675840000000, -28333505069110845063562564157123449813995764589839184000000⟩⟩
  | 0, 0, 0, 1 => ⟨⟨-22504192811927889811895914802100141751385498304000000000000, -22504192653547769030946471548330066061399876084000000000000⟩, ⟨-20454082952129508330487271983519327361927028928000000000000, -20454082839701537265133946191381434290577458808000000000000⟩⟩
  | 0, 0, 1, 0 => ⟨⟨-22504192811927889811895914802100141751385498304000000000000, -22504192653547769030946471548330066061399876084000000000000⟩, ⟨-20454082952129508330487271983519327361927028928000000000000, -20454082839701537265133946191381434290577458808000000000000⟩⟩
  | 0, 0, 1, 1 => ⟨⟨-27155895438185245898080858140570720152960000000000000000000, -27155895299738944140241881814129613757496000000000000000000⟩, ⟨13704873263043821121704226614953807630576000000000000000000, 13704873407365289554158575804715728542912000000000000000000⟩⟩
  | 0, 1, 0, 0 => ⟨⟨13526532342854346815810068987520478140073119110000000000000, 13526532433901956839000745768326771551580324072000000000000⟩, ⟨11525800688899508893224029560885019525062140160000000000000, 11525800785660224859086821061458737904166204474000000000000⟩⟩
  | 0, 1, 0, 1 => ⟨⟨15598181555915612506767893670758397323130000000000000000000, 15598181663549829263842783350483982827500000000000000000000⟩, ⟨-8508660503551453190661904428373662256812000000000000000000, -8508660397996372509070011573299409050718000000000000000000⟩⟩
  | 0, 1, 1, 0 => ⟨⟨15598181555915612506767893670758397323130000000000000000000, 15598181663549829263842783350483982827500000000000000000000⟩, ⟨-8508660503551453190661904428373662256812000000000000000000, -8508660397996372509070011573299409050718000000000000000000⟩⟩
  | 0, 1, 1, 1 => ⟨⟨-2368177402545632143632364359851388000000000000000000000000, -2368177299430504063371241653985794000000000000000000000000⟩, ⟨-17612577861977179086275849254689010000000000000000000000000, -17612577759613778385983839287596962000000000000000000000000⟩⟩
  | 1, 0, 0, 0 => ⟨⟨13526532342854346815810068987520478140073119110000000000000, 13526532433901956839000745768326771551580324072000000000000⟩, ⟨11525800688899508893224029560885019525062140160000000000000, 11525800785660224859086821061458737904166204474000000000000⟩⟩
  | 1, 0, 0, 1 => ⟨⟨15598181555915612506767893670758397323130000000000000000000, 15598181663549829263842783350483982827500000000000000000000⟩, ⟨-8508660503551453190661904428373662256812000000000000000000, -8508660397996372509070011573299409050718000000000000000000⟩⟩
  | 1, 0, 1, 0 => ⟨⟨15598181555915612506767893670758397323130000000000000000000, 15598181663549829263842783350483982827500000000000000000000⟩, ⟨-8508660503551453190661904428373662256812000000000000000000, -8508660397996372509070011573299409050718000000000000000000⟩⟩
  | 1, 0, 1, 1 => ⟨⟨-2368177402545632143632364359851388000000000000000000000000, -2368177299430504063371241653985794000000000000000000000000⟩, ⟨-17612577861977179086275849254689010000000000000000000000000, -17612577759613778385983839287596962000000000000000000000000⟩⟩
  | 1, 1, 0, 0 => ⟨⟨-26223950021060077053690810803216902766736000000000000000000, -26223949974090229027019409561464595241584000000000000000000⟩, ⟨15413327145092194343021435015107548136128000000000000000000, 15413327193558245822930186321877184011032000000000000000000⟩⟩
  | 1, 1, 0, 1 => ⟨⟨5014928675256852921824792266769456000000000000000000000000, 5014928720286625291974434587425592000000000000000000000000⟩, ⟨29994310931859728035094305247129344000000000000000000000000, 29994310967721491305147395764598528000000000000000000000000⟩⟩
  | 1, 1, 1, 0 => ⟨⟨5014928675256852921824792266769456000000000000000000000000, 5014928720286625291974434587425592000000000000000000000000⟩, ⟨29994310931859728035094305247129344000000000000000000000000, 29994310967721491305147395764598528000000000000000000000000⟩⟩
  | 1, 1, 1, 1 => ⟨⟨29807251003892065520778475148000000000000000000000000000000, 29807251022155428274663719772000000000000000000000000000000⟩, ⟨6043610401717696979974796004000000000000000000000000000000, 6043610434999989501967850436000000000000000000000000000000⟩⟩

def wagnerB3Val : Fin 2 → Fin 2 → Fin 2 → Fin 2 → CIntIv
  | 0, 0, 0, 0 => ⟨⟨24960855748690747061309140601415766113222805252652928000000, 24960855828862630755321649474795247406863190335442576000000⟩, ⟨10123045029796347657576533316384846949280697939189552000000, 10123045086963478917364170252154816571394571050342336000000⟩⟩
  | 0, 0, 0, 1 => ⟨⟨10455436519211424863967644714154898686240620160000000000000, 10455436573826784617120703601842316386895031080000000000000⟩, ⟨10262433058695160447200245693547090220498167584000000000000, 10262433125829333277037291653534733268326460816000000000000⟩⟩
  | 0, 0, 1, 0 => ⟨⟨10455436519211424863967644714154898686240620160000000000000, 10455436573826784617120703601842316386895031080000000000000⟩, ⟨10262433058695160447200245693547090220498167584000000000000, 10262433125829333277037291653534733268326460816000000000000⟩⟩
  | 0, 0, 1, 1 => ⟨⟨10593885964382471513569211963403240355120000000000000000000, 10593885999972071979311876900435038465312000000000000000000⟩, ⟨24780883681227021401783078673417112147776000000000000000000, 24780883718707327378501656225893987627664000000000000000000⟩⟩
  | 0, 1, 0, 0 => ⟨⟨-19005905555901044962763843822375270576807442576000000000000, -19005905467131277027803810487739763777568324120000000000000⟩, ⟨-19074046020574142195051108854324043103057660080000000000000, -19074045942779131191991297176862719257029320600000000000000⟩⟩
  | 0, 1, 0, 1 => ⟨⟨-5604956820951476697676252928747774369482000000000000000000, -5604956756900834576522721544940565142052000000000000000000⟩, ⟨-13526201149434800424882042134852435756902000000000000000000, -13526201079922429699680901808028024806522000000000000000000⟩⟩
  | 0, 1, 1, 0 => ⟨⟨-5604956820951476697676252928747774369482000000000000000000, -5604956756900834576522721544940565142052000000000000000000⟩, ⟨-13526201149434800424882042134852435756902000000000000000000, -13526201079922429699680901808028024806522000000000000000000⟩⟩
  | 0, 1, 1, 1 => ⟨⟨-55729286221036627263554222179816000000000000000000000000, -55729254827517446667416115330036000000000000000000000000⟩, ⟨-26926577408934546892371597468976744000000000000000000000000, -26926577379492198625835486495684452000000000000000000000000⟩⟩
  | 1, 0, 0, 0 => ⟨⟨-19005905555901044962763843822375270576807442576000000000000, -19005905467131277027803810487739763777568324120000000000000⟩, ⟨-19074046020574142195051108854324043103057660080000000000000, -19074045942779131191991297176862719257029320600000000000000⟩⟩
  | 1, 0, 0, 1 => ⟨⟨-5604956820951476697676252928747774369482000000000000000000, -5604956756900834576522721544940565142052000000000000000000⟩, ⟨-13526201149434800424882042134852435756902000000000000000000, -13526201079922429699680901808028024806522000000000000000000⟩⟩
  | 1, 0, 1, 0 => ⟨⟨-5604956820951476697676252928747774369482000000000000000000, -5604956756900834576522721544940565142052000000000000000000⟩, ⟨-13526201149434800424882042134852435756902000000000000000000, -13526201079922429699680901808028024806522000000000000000000⟩⟩
  | 1, 0, 1, 1 => ⟨⟨-55729286221036627263554222179816000000000000000000000000, -55729254827517446667416115330036000000000000000000000000⟩, ⟨-26926577408934546892371597468976744000000000000000000000000, -26926577379492198625835486495684452000000000000000000000000⟩⟩
  | 1, 1, 0, 0 => ⟨⟨10038732416554116879334396519351997817728000000000000000000, 10038732498813399216320667094449480288408000000000000000000⟩, ⟨25010926897149291195795042038317489058976000000000000000000, 25010926980141032568705487951275153958880000000000000000000⟩⟩
  | 1, 1, 0, 1 => ⟨⟨-132368189257913568434967874669392000000000000000000000000, -132368129164566535849014268167044000000000000000000000000⟩, ⟨14649783758483500589425481914373992000000000000000000000000, 14649783817199995976659083683419304000000000000000000000000⟩⟩
  | 1, 1, 1, 0 => ⟨⟨-132368189257913568434967874669392000000000000000000000000, -132368129164566535849014268167044000000000000000000000000⟩, ⟨14649783758483500589425481914373992000000000000000000000000, 14649783817199995976659083683419304000000000000000000000000⟩⟩
  | 1, 1, 1, 1 => ⟨⟨-10484963267568663178063296976000000000000000000000000000000, -10484963248014168808728667760000000000000000000000000000000⟩, ⟨24811003801082222073039033568000000000000000000000000000000, 24811003815293315477587098080000000000000000000000000000000⟩⟩

private lemma cert_wagnerB0_0000 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 0 0 0 = wagnerB0Val 0 0 0 0 := by decide
private lemma cert_wagnerB0_0001 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 0 0 1 = wagnerB0Val 0 0 0 1 := by decide
private lemma cert_wagnerB0_0010 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 0 1 0 = wagnerB0Val 0 0 1 0 := by decide
private lemma cert_wagnerB0_0011 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 0 1 1 = wagnerB0Val 0 0 1 1 := by decide
private lemma cert_wagnerB0_0100 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 1 0 0 = wagnerB0Val 0 1 0 0 := by decide
private lemma cert_wagnerB0_0101 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 1 0 1 = wagnerB0Val 0 1 0 1 := by decide
private lemma cert_wagnerB0_0110 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 1 1 0 = wagnerB0Val 0 1 1 0 := by decide
private lemma cert_wagnerB0_0111 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 0 1 1 1 = wagnerB0Val 0 1 1 1 := by decide
private lemma cert_wagnerB0_1000 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 0 0 0 = wagnerB0Val 1 0 0 0 := by decide
private lemma cert_wagnerB0_1001 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 0 0 1 = wagnerB0Val 1 0 0 1 := by decide
private lemma cert_wagnerB0_1010 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 0 1 0 = wagnerB0Val 1 0 1 0 := by decide
private lemma cert_wagnerB0_1011 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 0 1 1 = wagnerB0Val 1 0 1 1 := by decide
private lemma cert_wagnerB0_1100 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 1 0 0 = wagnerB0Val 1 1 0 0 := by decide
private lemma cert_wagnerB0_1101 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 1 0 1 = wagnerB0Val 1 1 0 1 := by decide
private lemma cert_wagnerB0_1110 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 1 1 0 = wagnerB0Val 1 1 1 0 := by decide
private lemma cert_wagnerB0_1111 : block2ValIv spinorsWagnerIv 0 4 1 7 3 5 1 1 1 1 = wagnerB0Val 1 1 1 1 := by decide

private lemma cert_wagnerB0_all : ∀ a b c d : Fin 2, block2ValIv spinorsWagnerIv 0 4 1 7 3 5 a b c d = wagnerB0Val a b c d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact cert_wagnerB0_0000
  · exact cert_wagnerB0_0001
  · exact cert_wagnerB0_0010
  · exact cert_wagnerB0_0011
  · exact cert_wagnerB0_0100
  · exact cert_wagnerB0_0101
  · exact cert_wagnerB0_0110
  · exact cert_wagnerB0_0111
  · exact cert_wagnerB0_1000
  · exact cert_wagnerB0_1001
  · exact cert_wagnerB0_1010
  · exact cert_wagnerB0_1011
  · exact cert_wagnerB0_1100
  · exact cert_wagnerB0_1101
  · exact cert_wagnerB0_1110
  · exact cert_wagnerB0_1111

private lemma cert_wagnerB1_0000 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 0 0 0 = wagnerB1Val 0 0 0 0 := by decide
private lemma cert_wagnerB1_0001 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 0 0 1 = wagnerB1Val 0 0 0 1 := by decide
private lemma cert_wagnerB1_0010 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 0 1 0 = wagnerB1Val 0 0 1 0 := by decide
private lemma cert_wagnerB1_0011 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 0 1 1 = wagnerB1Val 0 0 1 1 := by decide
private lemma cert_wagnerB1_0100 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 1 0 0 = wagnerB1Val 0 1 0 0 := by decide
private lemma cert_wagnerB1_0101 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 1 0 1 = wagnerB1Val 0 1 0 1 := by decide
private lemma cert_wagnerB1_0110 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 1 1 0 = wagnerB1Val 0 1 1 0 := by decide
private lemma cert_wagnerB1_0111 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 0 1 1 1 = wagnerB1Val 0 1 1 1 := by decide
private lemma cert_wagnerB1_1000 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 0 0 0 = wagnerB1Val 1 0 0 0 := by decide
private lemma cert_wagnerB1_1001 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 0 0 1 = wagnerB1Val 1 0 0 1 := by decide
private lemma cert_wagnerB1_1010 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 0 1 0 = wagnerB1Val 1 0 1 0 := by decide
private lemma cert_wagnerB1_1011 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 0 1 1 = wagnerB1Val 1 0 1 1 := by decide
private lemma cert_wagnerB1_1100 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 1 0 0 = wagnerB1Val 1 1 0 0 := by decide
private lemma cert_wagnerB1_1101 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 1 0 1 = wagnerB1Val 1 1 0 1 := by decide
private lemma cert_wagnerB1_1110 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 1 1 0 = wagnerB1Val 1 1 1 0 := by decide
private lemma cert_wagnerB1_1111 : block2ValIv spinorsWagnerIv 3 7 2 4 0 6 1 1 1 1 = wagnerB1Val 1 1 1 1 := by decide

private lemma cert_wagnerB1_all : ∀ a b c d : Fin 2, block2ValIv spinorsWagnerIv 3 7 2 4 0 6 a b c d = wagnerB1Val a b c d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact cert_wagnerB1_0000
  · exact cert_wagnerB1_0001
  · exact cert_wagnerB1_0010
  · exact cert_wagnerB1_0011
  · exact cert_wagnerB1_0100
  · exact cert_wagnerB1_0101
  · exact cert_wagnerB1_0110
  · exact cert_wagnerB1_0111
  · exact cert_wagnerB1_1000
  · exact cert_wagnerB1_1001
  · exact cert_wagnerB1_1010
  · exact cert_wagnerB1_1011
  · exact cert_wagnerB1_1100
  · exact cert_wagnerB1_1101
  · exact cert_wagnerB1_1110
  · exact cert_wagnerB1_1111

private lemma cert_wagnerB2_0000 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 0 0 0 = wagnerB2Val 0 0 0 0 := by decide
private lemma cert_wagnerB2_0001 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 0 0 1 = wagnerB2Val 0 0 0 1 := by decide
private lemma cert_wagnerB2_0010 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 0 1 0 = wagnerB2Val 0 0 1 0 := by decide
private lemma cert_wagnerB2_0011 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 0 1 1 = wagnerB2Val 0 0 1 1 := by decide
private lemma cert_wagnerB2_0100 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 1 0 0 = wagnerB2Val 0 1 0 0 := by decide
private lemma cert_wagnerB2_0101 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 1 0 1 = wagnerB2Val 0 1 0 1 := by decide
private lemma cert_wagnerB2_0110 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 1 1 0 = wagnerB2Val 0 1 1 0 := by decide
private lemma cert_wagnerB2_0111 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 0 1 1 1 = wagnerB2Val 0 1 1 1 := by decide
private lemma cert_wagnerB2_1000 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 0 0 0 = wagnerB2Val 1 0 0 0 := by decide
private lemma cert_wagnerB2_1001 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 0 0 1 = wagnerB2Val 1 0 0 1 := by decide
private lemma cert_wagnerB2_1010 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 0 1 0 = wagnerB2Val 1 0 1 0 := by decide
private lemma cert_wagnerB2_1011 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 0 1 1 = wagnerB2Val 1 0 1 1 := by decide
private lemma cert_wagnerB2_1100 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 1 0 0 = wagnerB2Val 1 1 0 0 := by decide
private lemma cert_wagnerB2_1101 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 1 0 1 = wagnerB2Val 1 1 0 1 := by decide
private lemma cert_wagnerB2_1110 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 1 1 0 = wagnerB2Val 1 1 1 0 := by decide
private lemma cert_wagnerB2_1111 : block2ValIv spinorsWagnerIv 1 2 0 5 3 6 1 1 1 1 = wagnerB2Val 1 1 1 1 := by decide

private lemma cert_wagnerB2_all : ∀ a b c d : Fin 2, block2ValIv spinorsWagnerIv 1 2 0 5 3 6 a b c d = wagnerB2Val a b c d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact cert_wagnerB2_0000
  · exact cert_wagnerB2_0001
  · exact cert_wagnerB2_0010
  · exact cert_wagnerB2_0011
  · exact cert_wagnerB2_0100
  · exact cert_wagnerB2_0101
  · exact cert_wagnerB2_0110
  · exact cert_wagnerB2_0111
  · exact cert_wagnerB2_1000
  · exact cert_wagnerB2_1001
  · exact cert_wagnerB2_1010
  · exact cert_wagnerB2_1011
  · exact cert_wagnerB2_1100
  · exact cert_wagnerB2_1101
  · exact cert_wagnerB2_1110
  · exact cert_wagnerB2_1111

private lemma cert_wagnerB3_0000 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 0 0 0 = wagnerB3Val 0 0 0 0 := by decide
private lemma cert_wagnerB3_0001 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 0 0 1 = wagnerB3Val 0 0 0 1 := by decide
private lemma cert_wagnerB3_0010 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 0 1 0 = wagnerB3Val 0 0 1 0 := by decide
private lemma cert_wagnerB3_0011 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 0 1 1 = wagnerB3Val 0 0 1 1 := by decide
private lemma cert_wagnerB3_0100 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 1 0 0 = wagnerB3Val 0 1 0 0 := by decide
private lemma cert_wagnerB3_0101 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 1 0 1 = wagnerB3Val 0 1 0 1 := by decide
private lemma cert_wagnerB3_0110 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 1 1 0 = wagnerB3Val 0 1 1 0 := by decide
private lemma cert_wagnerB3_0111 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 0 1 1 1 = wagnerB3Val 0 1 1 1 := by decide
private lemma cert_wagnerB3_1000 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 0 0 0 = wagnerB3Val 1 0 0 0 := by decide
private lemma cert_wagnerB3_1001 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 0 0 1 = wagnerB3Val 1 0 0 1 := by decide
private lemma cert_wagnerB3_1010 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 0 1 0 = wagnerB3Val 1 0 1 0 := by decide
private lemma cert_wagnerB3_1011 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 0 1 1 = wagnerB3Val 1 0 1 1 := by decide
private lemma cert_wagnerB3_1100 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 1 0 0 = wagnerB3Val 1 1 0 0 := by decide
private lemma cert_wagnerB3_1101 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 1 0 1 = wagnerB3Val 1 1 0 1 := by decide
private lemma cert_wagnerB3_1110 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 1 1 0 = wagnerB3Val 1 1 1 0 := by decide
private lemma cert_wagnerB3_1111 : block2ValIv spinorsWagnerIv 5 6 1 4 2 7 1 1 1 1 = wagnerB3Val 1 1 1 1 := by decide

private lemma cert_wagnerB3_all : ∀ a b c d : Fin 2, block2ValIv spinorsWagnerIv 5 6 1 4 2 7 a b c d = wagnerB3Val a b c d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact cert_wagnerB3_0000
  · exact cert_wagnerB3_0001
  · exact cert_wagnerB3_0010
  · exact cert_wagnerB3_0011
  · exact cert_wagnerB3_0100
  · exact cert_wagnerB3_0101
  · exact cert_wagnerB3_0110
  · exact cert_wagnerB3_0111
  · exact cert_wagnerB3_1000
  · exact cert_wagnerB3_1001
  · exact cert_wagnerB3_1010
  · exact cert_wagnerB3_1011
  · exact cert_wagnerB3_1100
  · exact cert_wagnerB3_1101
  · exact cert_wagnerB3_1110
  · exact cert_wagnerB3_1111

def wagnerLeftVal : (Fin 4 → Fin 2) → CIntIv
  | c => match c 0, c 1, c 2, c 3 with
    | 0, 0, 0, 0 => ⟨⟨2612102807015012903192665944037890331490846766215217693516627000000000000000000000000000000000000, 2612168405501952166022266494143369535835133047909844783065371000000000000000000000000000000000000⟩, ⟨-15775951343918620528871159692489708700771312735676114589800012000000000000000000000000000000000000, -15775884350132773749723306443167247463505308213859015359421684000000000000000000000000000000000000⟩⟩
    | 0, 0, 0, 1 => ⟨⟨1825474287028952959149336914381208947600365491651636014515611222654000000000000000000000000000000, 1825548781240293377233761893812514765666822895338350592085674222064000000000000000000000000000000⟩, ⟨5825221583739165412706110504369383047445360935454221548559103353714000000000000000000000000000000, 5825296758541485828322461998395606518589810843377428147233539149988000000000000000000000000000000⟩⟩
    | 0, 0, 1, 0 => ⟨⟨9911737880765473488763534195650536696191223342158645936000000000000000000000000000000000000000000, 9911812596658512338320227793708325276634511191370309996000000000000000000000000000000000000000000⟩, ⟨-16219406500714636978681053533068396291621637397522817972000000000000000000000000000000000000000000, -16219330932578148388790167812409453642016992837874283760000000000000000000000000000000000000000000⟩⟩
    | 0, 0, 1, 1 => ⟨⟨-574952993362446637627282921373881762928506616381263743681024000000000000000000000000000000000000, -574862792601951036002384412126221842961044483702302586612960000000000000000000000000000000000000⟩, ⟨6376912536403280400341024357287216125265235337668279453832232000000000000000000000000000000000000, 6377003653128266481482305232687565127474603743572518272706696000000000000000000000000000000000000⟩⟩
    | 0, 1, 0, 0 => ⟨⟨-14116865793278737803924857814708452873905822955087634381324078642990000000000000000000000000000000, -14116794220224485988885175073906620693622044474515994448601755855464000000000000000000000000000000⟩, ⟨-8986948123927848283737640287662277088056665584035341376279625640592000000000000000000000000000000, -8986877886421890892626307006783378560942865219952657649466185865738000000000000000000000000000000⟩⟩
    | 0, 1, 0, 1 => ⟨⟨5866767881679841774367506762380054114178422245444052775821076730232536004000000000000000000000000, 5866840577187128250253691952089830090602662306745066537584150047346665312000000000000000000000000⟩, ⟨538668389261511783816457302968367011153943779127213450931643939576886048000000000000000000000000, 538740441806103122678676719766457225581411736778503571899206381910757052000000000000000000000000⟩⟩
    | 0, 1, 1, 0 => ⟨⟨-11666798838553852261395279092918143298937901102641673212508947000000000000000000000000000000000000, -11666721782925800811778558172460381375763773416632232107188187000000000000000000000000000000000000⟩, ⟨-19542180251297266920753078258707985929935752305720610055357228000000000000000000000000000000000000, -19542102943610595918259557942463165291220248971378453436713588000000000000000000000000000000000000⟩⟩
    | 0, 1, 1, 1 => ⟨⟨6393457233928490990896674237998566399164913202767042919362814649056000000000000000000000000000000, 6393543152659176447879506558625420405059203415889882397819564415202000000000000000000000000000000⟩, ⟨3669207056104838550492817710775242074266078207220282534672342266556000000000000000000000000000000, 3669292947887922732589456893086100434718221010231793235670782451566000000000000000000000000000000⟩⟩
    | 1, 0, 0, 0 => ⟨⟨1669769648436664506730072727431173395898595607666780680000000000000000000000000000000000000000000, 1669838283093934683854855070291619015169208390843491644000000000000000000000000000000000000000000⟩, ⟨7179937978376210610849489412232667098791287509908354628000000000000000000000000000000000000000000, 7180006935901785864721486002853960407341729182830754952000000000000000000000000000000000000000000⟩⟩
    | 1, 0, 0, 1 => ⟨⟨-15347949504580257823490497329099604227630575290166586301485227000000000000000000000000000000000000, -15347879223993506667447862112693479006052450057163569662405411000000000000000000000000000000000000⟩, ⟨-16806287682560341292448090414816104726822476011636724836853452000000000000000000000000000000000000, -16806219225553588622493158192150303433328399363293863276534884000000000000000000000000000000000000⟩⟩
    | 1, 0, 1, 0 => ⟨⟨-1175921368056865974080049212822027889026656350288000000000000000000000000000000000000000000000000, -1175865107282786363010707771480526288226852788960000000000000000000000000000000000000000000000000⟩, ⟨5772915800568912807906135286256833894264940785104000000000000000000000000000000000000000000000000, 5772970679479797948174727087854131057355208728512000000000000000000000000000000000000000000000000⟩⟩
    | 1, 0, 1, 1 => ⟨⟨-4534568509770857977323001960379151760128001931758001228000000000000000000000000000000000000000000, -4534518229993856605512536994635899709153347221556557424000000000000000000000000000000000000000000⟩, ⟨-16108638159654062837365344009546279032101815851089482032000000000000000000000000000000000000000000, -16108587241320533164859758287464926222360438320356314348000000000000000000000000000000000000000000⟩⟩
    | 1, 1, 0, 0 => ⟨⟨6271830939757763234214296846461689867329703479010798971934184000000000000000000000000000000000000, 6271903788114206408201288984257194642727380828301483084751496000000000000000000000000000000000000⟩, ⟨1288295967791067242714133276026997296123948999258285074904576000000000000000000000000000000000000, 1288369414806736111129627650581197286907249159030292506457488000000000000000000000000000000000000⟩⟩
    | 1, 1, 0, 1 => ⟨⟨-18388565936468236971913833834188901864150678645967381066478290085896000000000000000000000000000000, -18388498622374240424793298385063682439563390834886388277336767791874000000000000000000000000000000⟩, ⟨4813812062082889898086829578116050913791437777554274469728962957738000000000000000000000000000000, 4813879900096377753354247473356318704425064769336443242698258548112000000000000000000000000000000⟩⟩
    | 1, 1, 1, 0 => ⟨⟨5051403824012906205330052820142522636305339834666144964000000000000000000000000000000000000000000, 5051460597784146690416277938984458285860351701579827768000000000000000000000000000000000000000000⟩, ⟨3427678041007557910452219910570479455183081618999150136000000000000000000000000000000000000000000, 3427736069277969184230801601327258305994210251429401404000000000000000000000000000000000000000000⟩⟩
    | 1, 1, 1, 1 => ⟨⟨-15859061267621528478635151428109743043341657224538421653656469000000000000000000000000000000000000, -15859014820736185875221696344325274393761681133214710554493277000000000000000000000000000000000000⟩, ⟨-2047886162827474338375234007188106724612827623891213255369500000000000000000000000000000000000000, -2047839175111041792377629226922560916172796488870252433373972000000000000000000000000000000000000⟩⟩

def wagnerRightVal : (Fin 4 → Fin 2) → CIntIv
  | c => match c 0, c 1, c 2, c 3 with
    | 0, 0, 0, 0 => ⟨⟨-418704700612660561510777265417566754837671122688819387609181494840389229053893088000000000000000000000000000000000000, -418704683995345065068878634674696418274534423105730732695270328635034813054356632000000000000000000000000000000000000⟩, ⟨-1042117106662862667060436624601405135444999248980005578241363954288134338418396688000000000000000000000000000000000000, -1042117089772959145486721203080078233640043981383917401923121725073621524199737040000000000000000000000000000000000000⟩⟩
    | 0, 0, 0, 1 => ⟨⟨-589266185656873333740316812305112016571628580722710570995936750468496429480000000000000000000000000000000000000000000, -589266173147303626287877462042405812935076753506015465135881598825820253072000000000000000000000000000000000000000000⟩, ⟨-956089017232065092345785767985523075504537633406033620906624457289207949904000000000000000000000000000000000000000000, -956089004919716015121880027716023217736255336544947320429921292643226120168000000000000000000000000000000000000000000⟩⟩
    | 0, 0, 1, 0 => ⟨⟨792741042199479403271693013105070410379879087235802233039930147623303906741764841733168000000000000000000000000000000, 792741058851015758077214493284685866891431502798083654723551203707276260563726228338884000000000000000000000000000000⟩, ⟨795659902929948699298174964761764453697135477090910087898953042350321105408439421424316000000000000000000000000000000, 795659920043729760917200060154768319663017147603347774007239562421919673424099425305236000000000000000000000000000000⟩⟩
    | 0, 0, 1, 1 => ⟨⟨916501585319298130133310837887103741813062757894695478178624217842576516124222644000000000000000000000000000000000000, 916501598651365424317820450127245593514429421781919210918975800633435943901301464000000000000000000000000000000000000⟩, ⟨650062524683998886641750244334511316650398049650872886393884242018721601048448668000000000000000000000000000000000000, 650062537598568189237970393495836897786631545702655846869047598536663887773550840000000000000000000000000000000000000⟩⟩
    | 0, 1, 0, 0 => ⟨⟨-1122986389241362560223517236496251007520966811087204004486287236244323513328000000000000000000000000000000000000000000, -1122986373750225018259638532127134352157327476523439547032189600459215322584000000000000000000000000000000000000000000⟩, ⟨18215109389807382823666713074489707543056185558866850010438488156898002856000000000000000000000000000000000000000000, 18215124575824355362973454478347101324803131485988579423853125315526373024000000000000000000000000000000000000000000⟩⟩
    | 0, 1, 0, 1 => ⟨⟨-1103457809052582513300938059874331071248644840394249051633577048615744000000000000000000000000000000000000000000000000, -1103457797298960052525881086381805916407453829745439997987474257675920000000000000000000000000000000000000000000000000⟩, ⟨208234850791309090000249148260766452063926154766954368799068795781248000000000000000000000000000000000000000000000000, 208234862874650768566051260164330815702547384311129271482276599741968000000000000000000000000000000000000000000000000⟩⟩
    | 0, 1, 1, 0 => ⟨⟨1026632863686699022794210451937754824148504394106992861946365131372484306863410672000000000000000000000000000000000000, 1026632879455304852034254846376196605908036790552430585628034564917603241144832316000000000000000000000000000000000000⟩, ⟨-455682340314394522490834397063714413082859995225532818872916629371736354870592368000000000000000000000000000000000000, -455682324961553801384374584136586870848632318126757411763599996427545155188981132000000000000000000000000000000000000⟩⟩
    | 0, 1, 1, 1 => ⟨⟨934762974896918903030866663306531207907426240495794626221483969410155267164000000000000000000000000000000000000000000, 934762987058447160662596575248620694186501217961788340996050940790134711812000000000000000000000000000000000000000000⟩, ⟨-623228820546653793302798993555048064182122282940982860192364027281592961700000000000000000000000000000000000000000000, -623228808037167266792373356615410569938918746208034680733282180378520028964000000000000000000000000000000000000000000⟩⟩
    | 1, 0, 0, 0 => ⟨⟨-410882416796136173093085714543409332459463609450576962619696025890955415189973736262980000000000000000000000000000000, -410882394711932121927368429981695976064380750439364775040954662730800337721554586204592000000000000000000000000000000⟩, ⟨1045644110552248757682830199377448177492367540640283701256994314044093604486993855543084000000000000000000000000000000, 1045644132051447835970897055130571781319404745249268133322889626589552662684749155220932000000000000000000000000000000⟩⟩
    | 1, 0, 0, 1 => ⟨⟨-227667361351232241700371930798023284456518904635822296432894395365164799475503384000000000000000000000000000000000000, -227667345061021114818977952209734090346687745641222447795667552784432816156863556000000000000000000000000000000000000⟩, ⟨1099904087256493568063043143173333529373162476397895039995762054555022054935522728000000000000000000000000000000000000, 1099904103030414569392788101312321814515902513637289996643444790321838496142352260000000000000000000000000000000000000⟩⟩
    | 1, 0, 1, 0 => ⟨⟨-30442681914445421813983816772466339596889123388890901601398377023588165013488626164748337200000000000000000000000000, -30442659123184701679739603110777837832908620080299563196404233476608185557444985842772933152000000000000000000000000⟩, ⟨-1122521332312416724226540803265735357922753453264281179054695797322700321617916613927895152096000000000000000000000000, -1122521310449983493023053988955327982704953141611260262555351762380903578387313948173403292704000000000000000000000000⟩⟩
    | 1, 0, 1, 1 => ⟨⟨-220283054161854075940366337670651146631560695827369564415117733768903637372377652761040000000000000000000000000000000, -220283035746150546645128276326149925703528109856927248855263750930594739348916449377392000000000000000000000000000000⟩, ⟨-1101319936644583162840490835636467725518284641434796652131145821664259065529445609926240000000000000000000000000000000, -1101319920004675276209215543820387293237439454349559938266947194914835144241407558647144000000000000000000000000000000⟩⟩
    | 1, 1, 0, 0 => ⟨⟨829592295995719837200996232710001853931460158117546734709201342328114264391912532000000000000000000000000000000000000, 829592317701977893962079802320972241519997688774001066745572201355939038392433232000000000000000000000000000000000000⟩, ⟨757847639127321030978150458245895170184009189197300082901800246279629864823105452000000000000000000000000000000000000, 757847661642296229677563378528743389848315585204911724295744250498811966921690384000000000000000000000000000000000000⟩⟩
    | 1, 1, 0, 1 => ⟨⟨945641451088390885675327080248541457871527492235864885216562632127730829340000000000000000000000000000000000000000000, 945641467765330694200443952394540854006103313750661741306172304520098473348000000000000000000000000000000000000000000⟩, ⟨606032415606092227344499953688326574159323174978757205631600363387509617796000000000000000000000000000000000000000000, 606032432791306659304435617685434713324765050831058526929949903563663190308000000000000000000000000000000000000000000⟩⟩
    | 1, 1, 1, 0 => ⟨⟨-1059284959157036600920805456130370326511156426691126602605754482031519789659867494287664000000000000000000000000000000, -1059284936585964971691690045071501740321830678394908406697034381674578274373091558059952000000000000000000000000000000⟩, ⟨-373170509808889853345591189648578860613428863129986919690965735966900500507755823947064000000000000000000000000000000, -373170486582754129565095791422863236163600434301814978339047224430623337407172465856768000000000000000000000000000000⟩⟩
    | 1, 1, 1, 1 => ⟨⟨-1107196715122824898527396526495550606515944695861729156699737218993077499336323152000000000000000000000000000000000000, -1107196697287469492402950187715449882730964035141760182789671906445647686160263264000000000000000000000000000000000000⟩, ⟨-188247507471038029428366324001459684052256001887425210915356150287743936135172160000000000000000000000000000000000000, -188247488526068291232210648890046164545474984244048364886279812151101905834227056000000000000000000000000000000000000⟩⟩

private lemma cert_wagnerLeft_0000 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 0, 0, 0] = wagnerLeftVal ![(0 : Fin 2), 0, 0, 0] := by decide
private lemma cert_wagnerLeft_0001 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 0, 0, 1] = wagnerLeftVal ![(0 : Fin 2), 0, 0, 1] := by decide
private lemma cert_wagnerLeft_0010 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 0, 1, 0] = wagnerLeftVal ![(0 : Fin 2), 0, 1, 0] := by decide
private lemma cert_wagnerLeft_0011 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 0, 1, 1] = wagnerLeftVal ![(0 : Fin 2), 0, 1, 1] := by decide
private lemma cert_wagnerLeft_0100 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 1, 0, 0] = wagnerLeftVal ![(0 : Fin 2), 1, 0, 0] := by decide
private lemma cert_wagnerLeft_0101 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 1, 0, 1] = wagnerLeftVal ![(0 : Fin 2), 1, 0, 1] := by decide
private lemma cert_wagnerLeft_0110 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 1, 1, 0] = wagnerLeftVal ![(0 : Fin 2), 1, 1, 0] := by decide
private lemma cert_wagnerLeft_0111 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(0 : Fin 2), 1, 1, 1] = wagnerLeftVal ![(0 : Fin 2), 1, 1, 1] := by decide
private lemma cert_wagnerLeft_1000 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 0, 0, 0] = wagnerLeftVal ![(1 : Fin 2), 0, 0, 0] := by decide
private lemma cert_wagnerLeft_1001 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 0, 0, 1] = wagnerLeftVal ![(1 : Fin 2), 0, 0, 1] := by decide
private lemma cert_wagnerLeft_1010 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 0, 1, 0] = wagnerLeftVal ![(1 : Fin 2), 0, 1, 0] := by decide
private lemma cert_wagnerLeft_1011 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 0, 1, 1] = wagnerLeftVal ![(1 : Fin 2), 0, 1, 1] := by decide
private lemma cert_wagnerLeft_1100 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 1, 0, 0] = wagnerLeftVal ![(1 : Fin 2), 1, 0, 0] := by decide
private lemma cert_wagnerLeft_1101 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 1, 0, 1] = wagnerLeftVal ![(1 : Fin 2), 1, 0, 1] := by decide
private lemma cert_wagnerLeft_1110 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 1, 1, 0] = wagnerLeftVal ![(1 : Fin 2), 1, 1, 0] := by decide
private lemma cert_wagnerLeft_1111 : leftHalf8TabsIv wagnerB0Val wagnerB1Val ![(1 : Fin 2), 1, 1, 1] = wagnerLeftVal ![(1 : Fin 2), 1, 1, 1] := by decide
private lemma cert_wagnerLeft_all : ∀ c : Fin 4 → Fin 2, leftHalf8TabsIv wagnerB0Val wagnerB1Val c = wagnerLeftVal c := by
  intro c
  have hc : c = ![c 0, c 1, c 2, c 3] := by ext i; fin_cases i <;> rfl
  rw [hc]
  rcases fin2_cases (c 0) with h0 | h0 <;> rcases fin2_cases (c 1) with h1 | h1 <;> rcases fin2_cases (c 2) with h2 | h2 <;> rcases fin2_cases (c 3) with h3 | h3 <;> rw [h0, h1, h2, h3]
  · exact cert_wagnerLeft_0000
  · exact cert_wagnerLeft_0001
  · exact cert_wagnerLeft_0010
  · exact cert_wagnerLeft_0011
  · exact cert_wagnerLeft_0100
  · exact cert_wagnerLeft_0101
  · exact cert_wagnerLeft_0110
  · exact cert_wagnerLeft_0111
  · exact cert_wagnerLeft_1000
  · exact cert_wagnerLeft_1001
  · exact cert_wagnerLeft_1010
  · exact cert_wagnerLeft_1011
  · exact cert_wagnerLeft_1100
  · exact cert_wagnerLeft_1101
  · exact cert_wagnerLeft_1110
  · exact cert_wagnerLeft_1111

private lemma cert_wagnerRight_0000 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 0, 0, 0] = wagnerRightVal ![(0 : Fin 2), 0, 0, 0] := by decide
private lemma cert_wagnerRight_0001 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 0, 0, 1] = wagnerRightVal ![(0 : Fin 2), 0, 0, 1] := by decide
private lemma cert_wagnerRight_0010 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 0, 1, 0] = wagnerRightVal ![(0 : Fin 2), 0, 1, 0] := by decide
private lemma cert_wagnerRight_0011 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 0, 1, 1] = wagnerRightVal ![(0 : Fin 2), 0, 1, 1] := by decide
private lemma cert_wagnerRight_0100 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 1, 0, 0] = wagnerRightVal ![(0 : Fin 2), 1, 0, 0] := by decide
private lemma cert_wagnerRight_0101 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 1, 0, 1] = wagnerRightVal ![(0 : Fin 2), 1, 0, 1] := by decide
private lemma cert_wagnerRight_0110 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 1, 1, 0] = wagnerRightVal ![(0 : Fin 2), 1, 1, 0] := by decide
private lemma cert_wagnerRight_0111 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(0 : Fin 2), 1, 1, 1] = wagnerRightVal ![(0 : Fin 2), 1, 1, 1] := by decide
private lemma cert_wagnerRight_1000 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 0, 0, 0] = wagnerRightVal ![(1 : Fin 2), 0, 0, 0] := by decide
private lemma cert_wagnerRight_1001 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 0, 0, 1] = wagnerRightVal ![(1 : Fin 2), 0, 0, 1] := by decide
private lemma cert_wagnerRight_1010 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 0, 1, 0] = wagnerRightVal ![(1 : Fin 2), 0, 1, 0] := by decide
private lemma cert_wagnerRight_1011 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 0, 1, 1] = wagnerRightVal ![(1 : Fin 2), 0, 1, 1] := by decide
private lemma cert_wagnerRight_1100 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 1, 0, 0] = wagnerRightVal ![(1 : Fin 2), 1, 0, 0] := by decide
private lemma cert_wagnerRight_1101 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 1, 0, 1] = wagnerRightVal ![(1 : Fin 2), 1, 0, 1] := by decide
private lemma cert_wagnerRight_1110 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 1, 1, 0] = wagnerRightVal ![(1 : Fin 2), 1, 1, 0] := by decide
private lemma cert_wagnerRight_1111 : rightHalf8TabsIv wagnerB2Val wagnerB3Val ![(1 : Fin 2), 1, 1, 1] = wagnerRightVal ![(1 : Fin 2), 1, 1, 1] := by decide
private lemma cert_wagnerRight_all : ∀ c : Fin 4 → Fin 2, rightHalf8TabsIv wagnerB2Val wagnerB3Val c = wagnerRightVal c := by
  intro c
  have hc : c = ![c 0, c 1, c 2, c 3] := by ext i; fin_cases i <;> rfl
  rw [hc]
  rcases fin2_cases (c 0) with h0 | h0 <;> rcases fin2_cases (c 1) with h1 | h1 <;> rcases fin2_cases (c 2) with h2 | h2 <;> rcases fin2_cases (c 3) with h3 | h3 <;> rw [h0, h1, h2, h3]
  · exact cert_wagnerRight_0000
  · exact cert_wagnerRight_0001
  · exact cert_wagnerRight_0010
  · exact cert_wagnerRight_0011
  · exact cert_wagnerRight_0100
  · exact cert_wagnerRight_0101
  · exact cert_wagnerRight_0110
  · exact cert_wagnerRight_0111
  · exact cert_wagnerRight_1000
  · exact cert_wagnerRight_1001
  · exact cert_wagnerRight_1010
  · exact cert_wagnerRight_1011
  · exact cert_wagnerRight_1100
  · exact cert_wagnerRight_1101
  · exact cert_wagnerRight_1110
  · exact cert_wagnerRight_1111

def wagnerNumIv' : CIntIv := wagnerNumIv spinorsWagnerIv
def wagnerDenIv' : CIntIv := wagnerDenIv spinorsWagnerIv
def wagnerNumVal : CIntIv := ⟨⟨-2272706600401948670217143107139526236948609680275215264042109974518848851828057599041873913779495548817148668349684211329797379214899284760000000000000000000000000000000000000000000000000000000000000000000000000, -684086247827599985219642212046159385882960885367989031945577869837064998448504794835751969651926843679720099567678151088062127424242153536000000000000000000000000000000000000000000000000000000000000000000000000⟩, ⟨36717773412301108988142047260241481298092026220035305957617358994639848003658339317444639055253948772017833575431926638588606327301285370296000000000000000000000000000000000000000000000000000000000000000000000000, 38307568274919512563064200216190310263621523693126752542270314625481878583561543931599492939300920506666288928446116270094329645777454734152000000000000000000000000000000000000000000000000000000000000000000000000⟩⟩
def wagnerDenVal : CIntIv := ⟨⟨995655542617661627474194548381937630722844343298953656254421013375504371638986092054496334536746031725424978646532304490187980725161033728000000000000000000000000000000000000000000000000000000000000000000000000, 995699727694213119567475672930880086705011466092976200120758566985522322822724582908114634278625484399545860845088012535664875059648921600000000000000000000000000000000000000000000000000000000000000000000000000⟩, ⟨-25233543102777377457008623420701706472813245337166512052162700830091534191288959294227090337023700284329694998834993342548793400008181284864000000000000000000000000000000000000000000000000000000000000000000000000, -25233498920619189909373896945368550852405134134009441269967195162097561678101566054449348366689869676632486238664416884688050284558001635328000000000000000000000000000000000000000000000000000000000000000000000000⟩⟩

theorem cert_wagner_num_val : wagnerNumIv' = wagnerNumVal := by
  dsimp only [wagnerNumIv', wagnerNumIv]
  have ht0 : (fun a b c d => block2ValIv spinorsWagnerIv 0 4 1 7 3 5 a b c d) = wagnerB0Val := by
    funext a b c d; exact cert_wagnerB0_all a b c d
  have ht1 : (fun a b c d => block2ValIv spinorsWagnerIv 3 7 2 4 0 6 a b c d) = wagnerB1Val := by
    funext a b c d; exact cert_wagnerB1_all a b c d
  have ht2 : (fun a b c d => block2ValIv spinorsWagnerIv 1 2 0 5 3 6 a b c d) = wagnerB2Val := by
    funext a b c d; exact cert_wagnerB2_all a b c d
  have ht3 : (fun a b c d => block2ValIv spinorsWagnerIv 5 6 1 4 2 7 a b c d) = wagnerB3Val := by
    funext a b c d; exact cert_wagnerB3_all a b c d
  have hl : leftHalf8TabsIv wagnerB0Val wagnerB1Val = wagnerLeftVal := funext cert_wagnerLeft_all
  have hr : rightHalf8TabsIv wagnerB2Val wagnerB3Val = wagnerRightVal := funext cert_wagnerRight_all
  rw [ht0, ht1, ht2, ht3, hl, hr]
  decide

theorem cert_wagner_den_val : wagnerDenIv' = wagnerDenVal := by decide

theorem cert_wagner_dot_neg :
    ((wagnerNumVal.re.mul wagnerDenVal.re).add (wagnerNumVal.im.mul wagnerDenVal.im)).hi < 0 := by decide

def wagnerPoint (t : ℝ) (u : Fin 8) : Fin 3 → ℝ
  | 0 => (wagnerPtsX u : ℝ)
  | 1 => (wagnerPtsY u : ℝ) * t
  | 2 => 0

def wagnerPath (t : ℝ) : ConfigSpace wagnerGraph :=
  ⟨wagnerPoint t, by
    intro u v huv h
    have hx : (wagnerPtsX u : ℝ) = (wagnerPtsX v : ℝ) := congr_fun h 0
    exact wagnerGraph.ne_of_adj huv (wagnerPtsX_inj (Int.cast_injective hx))⟩

lemma wagnerPath_planar (t : ℝ) (u : Fin 8) : (wagnerPath t).1 u 2 = 0 := rfl

private lemma malkounAmplitudeOfSpinors_congr {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (ψ₁ ψ₂ : Fin m → Fin m → Fin 2 → ℂ) (h : ∀ u v, G.Adj u v → ∀ k, ψ₁ u v k = ψ₂ u v k) :
    malkounAmplitudeOfSpinors G ψ₁ = malkounAmplitudeOfSpinors G ψ₂ := by
  have h1 : ∀ u v, G.Adj u v → ψ₁ u v = ψ₂ u v := fun u v huv => funext (h u v huv)
  have hnum : malkounNum G ψ₁ = malkounNum G ψ₂ := by
    refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => ?_
    rw [h1 _ _ (σ e.1.1 ⟨e.1.2, e.2.1⟩).2, h1 _ _ (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).2]
  have hden : malkounDen G ψ₁ = malkounDen G ψ₂ := by
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [h1 _ _ e.2.1, h1 _ _ e.2.1.symm]
  simp only [malkounAmplitudeOfSpinors, hnum, hden]

private lemma match_collinear_wagner (u v : Fin 8) (dx r g : ℤ) (s : Fin 2 → GI)
    (hr_nn : 0 ≤ r) (hpt0 : wagnerPoint 0 v 0 - wagnerPoint 0 u 0 = (dx : ℝ))
    (hpt1 : wagnerPoint 0 v 1 - wagnerPoint 0 u 1 = 0) (hr_sq : r * r = dx * dx)
    (h0re : r = g * (s 0).re) (h0im : (s 0).im = 0)
    (h1re : dx = g * (s 1).re) (h1im : 0 = g * (s 1).im) :
    ∀ k : Fin 2, planarUnnormSpinor (wagnerPoint 0 u) (wagnerPoint 0 v) k = ((g : ℤ) : ℂ) * GI.toC (s k) := by
  have hr_R : (r : ℝ) ^ 2 = (wagnerPoint 0 v 0 - wagnerPoint 0 u 0) ^ 2 +
      (wagnerPoint 0 v 1 - wagnerPoint 0 u 1) ^ 2 + (wagnerPoint 0 v 2 - wagnerPoint 0 u 2) ^ 2 := by
    rw [hpt0, hpt1]
    simp only [wagnerPoint, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    have hsq : (r : ℝ) * (r : ℝ) = (dx : ℝ) * (dx : ℝ) := by exact_mod_cast hr_sq
    linarith [sq (r : ℝ), sq (dx : ℝ)]
  have heuclid : euclidNorm (fun j => wagnerPoint 0 v j - wagnerPoint 0 u j) = (r : ℝ) := by
    rw [euclidNorm, ← hr_R]; exact Real.sqrt_sq (by exact_mod_cast hr_nn)
  intro k; rcases fin2_cases k with rfl | rfl
  · simp only [planarUnnormSpinor, heuclid, GI.toC, h0im, Int.cast_zero, mul_zero, add_zero]; exact_mod_cast h0re
  · simp only [planarUnnormSpinor, hpt0, hpt1, Complex.ofReal_zero, mul_zero, add_zero, GI.toC]
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.add_re, Complex.I_re, zero_mul, Complex.I_im, mul_zero, sub_self, add_zero, sub_zero]
      exact_mod_cast h1re
    · simp only [Complex.ofReal_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        Complex.add_im, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_add, add_zero]
      exact_mod_cast h1im

theorem malkounAmplitude_wagnerPath_zero : malkounAmplitude wagnerGraph (wagnerPath 0) = 2304 := by
  have hmatch : ∀ u v, wagnerGraph.Adj u v → ∀ k, planarUnnormSpinor (wagnerPoint 0 u) (wagnerPoint 0 v) k =
      ((scaleFromInts ((wagnerPtsX v - wagnerPtsX u).natAbs : ℤ) (wagnerPtsX v - wagnerPtsX u) 0 : ℤ) : ℂ) * GI.toC (spinorsWagnerColGI u v k) := by
    intro u v huv
    rcases spinorsWagnerColGI_ok u v huv with ⟨_, hr_nn, hr_sq, h0re, h0im, h1re, h1im⟩
    exact match_collinear_wagner u v (wagnerPtsX v - wagnerPtsX u) ((wagnerPtsX v - wagnerPtsX u).natAbs : ℤ)
      _ (spinorsWagnerColGI u v) hr_nn (by simp [wagnerPoint, Int.cast_sub]) (by simp [wagnerPoint])
      hr_sq h0re h0im h1re h1im
  have hscale : ∀ u v, wagnerGraph.Adj u v → scaleFromInts ((wagnerPtsX v - wagnerPtsX u).natAbs : ℤ) (wagnerPtsX v - wagnerPtsX u) 0 ≠ 0 :=
    fun u v huv => (spinorsWagnerColGI_ok u v huv).1
  rw [malkounAmplitude_eq_planarUnnorm wagnerGraph (wagnerPath 0) (wagnerPath_planar 0)]
  change malkounAmplitudeOfSpinors wagnerGraph (fun u v => planarUnnormSpinor (wagnerPoint 0 u) (wagnerPoint 0 v)) = 2304
  rw [malkounAmplitudeOfSpinors_congr wagnerGraph _ _ hmatch]
  rw [malkounAmplitude_scale_invariant wagnerGraph _ (fun u v huv => Int.cast_ne_zero.mpr (hscale u v huv)) (fun u v k => GI.toC (spinorsWagnerColGI u v k))]
  simp only [malkounAmplitudeOfSpinors, ← malkounNum_wagner_giToC, ← malkounDen_wagner_giToC, cert_wagner_col_num, cert_wagner_col_den, GI.toC_ofInt]
  norm_num

private lemma nonneg_sq_le_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b := by
  constructor
  · intro hab; exact mul_self_le_mul_self ha hab
  · intro hsq; by_contra! hlt
    have hpos : 0 < (a - b) * (a + b) := mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg (lt_of_le_of_lt hb hlt) hb)
    linarith

private noncomputable def wagnerScaledSpinors (u v : Fin 8) (k : Fin 2) : ℂ :=
  ((wagnerScale : ℤ) : ℂ) * planarUnnormSpinor (wagnerPoint 1 u) (wagnerPoint 1 v) k

private lemma spinorsWagnerIv_mem : ∀ u v : Fin 8, wagnerGraph.Adj u v →
    ∀ k : Fin 2, (spinorsWagnerIv u v k).Mem (wagnerScaledSpinors u v k) := by
  intro u v huv k
  rcases distWagnerLo_ok u v huv with ⟨hlo_nn, hlo_sq, hhi_sq⟩
  let dx := wagnerPtsX v - wagnerPtsX u
  let dy := wagnerPtsY v - wagnerPtsY u
  let r_real := euclidNorm (fun j => wagnerPoint 1 v j - wagnerPoint 1 u j)
  have hS_pos : (0 : ℝ) < (wagnerScale : ℝ) := by norm_num [wagnerScale]
  have hr_nn : 0 ≤ r_real := Real.sqrt_nonneg _
  have hr_sq : ((wagnerScale : ℝ) * r_real) * ((wagnerScale : ℝ) * r_real) = ((wagnerScale * wagnerScale * (dx * dx + dy * dy) : ℤ) : ℝ) := by
    have hnorm_sq : r_real * r_real = (dx : ℝ) * (dx : ℝ) + (dy : ℝ) * (dy : ℝ) := by
      simp only [r_real, euclidNorm, ← sq]; rw [Real.sq_sqrt (by positivity)]
      simp only [wagnerPoint, mul_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, dx, dy]
      push_cast; ring
    calc ((wagnerScale : ℝ) * r_real) * ((wagnerScale : ℝ) * r_real) = (wagnerScale : ℝ) * (wagnerScale : ℝ) * (r_real * r_real) := by ring
      _ = ((wagnerScale * wagnerScale * (dx * dx + dy * dy) : ℤ) : ℝ) := by rw [hnorm_sq]; push_cast; ring
  have hlo_R : (distWagnerLo u v : ℝ) ≤ (wagnerScale : ℝ) * r_real := by
    refine (nonneg_sq_le_iff (by exact_mod_cast hlo_nn) (mul_nonneg hS_pos.le hr_nn)).mpr ?_
    rw [hr_sq]; exact_mod_cast hlo_sq
  have hhi_R : (wagnerScale : ℝ) * r_real ≤ ((distWagnerLo u v + 1 : ℤ) : ℝ) := by
    refine (nonneg_sq_le_iff (mul_nonneg hS_pos.le hr_nn) (by exact_mod_cast (by omega : 0 ≤ distWagnerLo u v + 1))).mpr ?_
    rw [hr_sq]; exact_mod_cast hhi_sq
  rcases fin2_cases k with rfl | rfl
  · simp only [wagnerScaledSpinors, planarUnnormSpinor, spinorsWagnerIv, CIntIv.Mem, IntIv.Mem, IntIv.zero]
    have hre : (((wagnerScale : ℤ) : ℂ) * (r_real : ℂ)).re = (wagnerScale : ℝ) * r_real := by
      change ((wagnerScale : ℝ) * (r_real : ℂ)).re = _; simp
    have him : (((wagnerScale : ℤ) : ℂ) * (r_real : ℂ)).im = 0 := by
      change ((wagnerScale : ℝ) * (r_real : ℂ)).im = _; simp
    rw [hre, him]; exact ⟨⟨hlo_R, by exact_mod_cast hhi_R⟩, ⟨le_rfl, le_rfl⟩⟩
  · simp only [wagnerScaledSpinors, planarUnnormSpinor, spinorsWagnerIv, CIntIv.Mem]
    have hdx_r : wagnerPoint 1 v 0 - wagnerPoint 1 u 0 = (dx : ℝ) := by simp [wagnerPoint, dx]
    have hdy_r : wagnerPoint 1 v 1 - wagnerPoint 1 u 1 = (dy : ℝ) := by simp [wagnerPoint, dy]
    rw [hdx_r, hdy_r]
    have hre : (((wagnerScale : ℤ) : ℂ) * (((dx : ℝ) : ℂ) + Complex.I * ((dy : ℝ) : ℂ))).re = ((wagnerScale * dx : ℤ) : ℝ) := by push_cast; simp
    have him : (((wagnerScale : ℤ) : ℂ) * (((dx : ℝ) : ℂ) + Complex.I * ((dy : ℝ) : ℂ))).im = ((wagnerScale * dy : ℤ) : ℝ) := by push_cast; simp
    change (IntIv.ofInt (wagnerScale * dx)).Mem _ ∧ (IntIv.ofInt (wagnerScale * dy)).Mem _
    rw [hre, him]; exact ⟨IntIv.ofInt_mem _, IntIv.ofInt_mem _⟩

private lemma div_re_neg_of_iv_dot_neg {N D : ℂ} {numIv denIv : CIntIv}
    (hD : D ≠ 0) (hN_mem : numIv.Mem N) (hD_mem : denIv.Mem D)
    (hdot : ((numIv.re.mul denIv.re).add (numIv.im.mul denIv.im)).hi < 0) : (N / D).re < 0 := by
  have hdot_mem := IntIv.add_mem (IntIv.mul_mem hN_mem.1 hD_mem.1) (IntIv.mul_mem hN_mem.2 hD_mem.2)
  have hneg : N.re * D.re + N.im * D.im < 0 := lt_of_le_of_lt hdot_mem.2 (Int.cast_lt.mpr hdot)
  have hre : (N / D).re = (N.re * D.re + N.im * D.im) / Complex.normSq D := by rw [Complex.div_re]; ring
  rw [hre]; exact div_neg_of_neg_of_pos hneg (Complex.normSq_pos.mpr hD)

@[irreducible] private noncomputable def wagnerNumC : ℂ := malkounNum wagnerGraph wagnerScaledSpinors
@[irreducible] private noncomputable def wagnerDenC : ℂ := malkounDen wagnerGraph wagnerScaledSpinors

/-- Value of $\mathcal{A}_{M_8}(\gamma(1))$ shielded as `@[irreducible]` so `LT.lt` on `ℝ` does not unfold `malkounNum`. -/
@[irreducible] noncomputable def wagnerAmpOne : ℂ := malkounAmplitude wagnerGraph (wagnerPath 1)

lemma wagnerAmpOne_eq : wagnerAmpOne = malkounAmplitude wagnerGraph (wagnerPath 1) := by unfold wagnerAmpOne; rfl
private lemma wagnerNumC_eq : wagnerNumC = malkounNum wagnerGraph wagnerScaledSpinors := by unfold wagnerNumC; rfl
private lemma wagnerDenC_eq : wagnerDenC = malkounDen wagnerGraph wagnerScaledSpinors := by unfold wagnerDenC; rfl

theorem wagnerAmpOne_re_neg : wagnerAmpOne.re < 0 := by
  have hS_ne : ((wagnerScale : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by decide)
  have hamp : wagnerAmpOne = wagnerNumC / wagnerDenC := by
    rw [wagnerAmpOne_eq, wagnerNumC_eq, wagnerDenC_eq]
    rw [malkounAmplitude_eq_planarUnnorm wagnerGraph (wagnerPath 1) (wagnerPath_planar 1)]
    exact (malkounAmplitude_scale_invariant wagnerGraph (fun _ _ => ((wagnerScale : ℤ) : ℂ)) (fun _ _ _ => hS_ne) (fun u v => planarUnnormSpinor (wagnerPoint 1 u) (wagnerPoint 1 v))).symm
  have hden_ne : wagnerDenC ≠ 0 := by
    rw [wagnerDenC_eq]
    have hden0 := malkounDen_planarUnnorm_ne_zero wagnerGraph (wagnerPath 1) (wagnerPath_planar 1)
    have hfactor : malkounDen wagnerGraph wagnerScaledSpinors =
        ∏ _e : OriEdge wagnerGraph, ((wagnerScale : ℤ) : ℂ) * ((wagnerScale : ℤ) : ℂ) *
          omega (planarUnnormSpinor (wagnerPoint 1 _e.1.1) (wagnerPoint 1 _e.1.2)) (planarUnnormSpinor (wagnerPoint 1 _e.1.2) (wagnerPoint 1 _e.1.1)) := by
      refine Finset.prod_congr rfl fun e _ => ?_
      change omega (fun k => ((wagnerScale : ℤ) : ℂ) * planarUnnormSpinor (wagnerPoint 1 e.1.1) (wagnerPoint 1 e.1.2) k)
                   (fun k => ((wagnerScale : ℤ) : ℂ) * planarUnnormSpinor (wagnerPoint 1 e.1.2) (wagnerPoint 1 e.1.1) k) = _
      rw [omega_smul]
    rw [hfactor, Finset.prod_mul_distrib]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ => mul_ne_zero hS_ne hS_ne) hden0
  have hN : wagnerNumVal.Mem wagnerNumC := by
    rw [wagnerNumC_eq, ← cert_wagner_num_val]
    exact wagnerNumIv_mem spinorsWagnerIv wagnerScaledSpinors spinorsWagnerIv_mem
  have hD : wagnerDenVal.Mem wagnerDenC := by
    rw [wagnerDenC_eq, ← cert_wagner_den_val]
    exact wagnerDenIv_mem spinorsWagnerIv wagnerScaledSpinors spinorsWagnerIv_mem
  rw [hamp]; exact div_re_neg_of_iv_dot_neg hden_ne hN hD cert_wagner_dot_neg

private lemma continuous_planarUnnorm_wagnerPath (u v : Fin 8) (k : Fin 2) :
    Continuous (fun t : ℝ => planarUnnormSpinor (wagnerPoint t u) (wagnerPoint t v) k) := by
  fin_cases k
  · dsimp [planarUnnormSpinor, euclidNorm, wagnerPoint]; fun_prop
  · dsimp [planarUnnormSpinor, wagnerPoint]; fun_prop

theorem continuous_malkounAmplitude_wagnerPath :
    Continuous (fun t : ℝ => malkounAmplitude wagnerGraph (wagnerPath t)) := by
  have hfun : (fun t : ℝ => malkounAmplitude wagnerGraph (wagnerPath t)) =
      fun t : ℝ => malkounNum wagnerGraph (fun u v => planarUnnormSpinor (wagnerPoint t u) (wagnerPoint t v)) /
        malkounDen wagnerGraph (fun u v => planarUnnormSpinor (wagnerPoint t u) (wagnerPoint t v)) := by
    ext t; exact malkounAmplitude_eq_planarUnnorm wagnerGraph (wagnerPath t) (wagnerPath_planar t)
  rw [hfun]
  have hspin : ∀ u v k, Continuous (fun t : ℝ => planarUnnormSpinor (wagnerPoint t u) (wagnerPoint t v) k) :=
    continuous_planarUnnorm_wagnerPath
  have homega : ∀ (f g : Fin 2 → ℝ → ℂ), (∀ k, Continuous (f k)) → (∀ k, Continuous (g k)) →
      Continuous (fun t => omega (fun k => f k t) (fun k => g k t)) := fun f g hf hg => by dsimp [omega]; fun_prop
  have hnum : Continuous (fun t : ℝ => malkounNum wagnerGraph (fun u v => planarUnnormSpinor (wagnerPoint t u) (wagnerPoint t v))) := by
    dsimp [malkounNum]; fun_prop (disch := exact fun _ _ _ => _)
  have hden : Continuous (fun t : ℝ => malkounDen wagnerGraph (fun u v => planarUnnormSpinor (wagnerPoint t u) (wagnerPoint t v))) := by
    dsimp [malkounDen]; fun_prop
  exact hnum.div hden fun t => malkounDen_planarUnnorm_ne_zero wagnerGraph (wagnerPath t) (wagnerPath_planar t)

private lemma exists_wagnerPath_zero :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) 1, malkounAmplitude wagnerGraph (wagnerPath t₀) = 0 := by
  let f : ℝ → ℝ := fun t => (malkounAmplitude wagnerGraph (wagnerPath t)).re
  have hf_cont : Continuous f := Complex.continuous_re.comp continuous_malkounAmplitude_wagnerPath
  have h0 : f 0 = 2304 := by dsimp only [f]; rw [malkounAmplitude_wagnerPath_zero]; norm_num
  have h1_eq : f 1 = wagnerAmpOne.re := by dsimp only [f]; rw [← wagnerAmpOne_eq]
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
    refine ⟨?_, by rw [h0]; norm_num⟩
    rw [h1_eq]; exact wagnerAmpOne_re_neg.le
  rcases intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf_cont.continuousOn hmem with ⟨t₀, ht₀_icc, ht₀_re⟩
  refine ⟨t₀, ht₀_icc, ?_⟩
  have ht₀_im : (malkounAmplitude wagnerGraph (wagnerPath t₀)).im = 0 :=
    planar_amplitude_im_eq_zero wagnerGraph (wagnerPath t₀) (wagnerPath_planar t₀)
  exact Complex.ext (by simpa [f] using ht₀_re) ht₀_im

/-- **Formal Disproof of Malkoun's Conjecture A on the triangle-free, 3-regular, 3-connected Wagner graph $M_8$.** -/
theorem disproof_malkoun_wagner_triangleFree_conjecture_A :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ IsThreeVertexConnected G ∧ G.IsRegularOfDegree 3 ∧ G.CliqueFree 3 ∧
        ∃ x : ConfigSpace G, malkounAmplitude G x = 0 := by
  rcases exists_wagnerPath_zero with ⟨t₀, _, ht₀⟩
  exact ⟨8, wagnerGraph, instDecidableRelWagner, wagnerGraph_connected,
    wagnerGraph_threeVertexConnected, wagnerGraph_isRegularOfDegree_three,
    wagnerGraph_cliqueFree_three, wagnerPath t₀, ht₀⟩

/-- **Formal Disproof of Malkoun's Conjecture B on the triangle-free, 3-regular, 3-connected Wagner graph $M_8$.** -/
theorem disproof_malkoun_wagner_triangleFree_conjecture_B :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ IsThreeVertexConnected G ∧ G.IsRegularOfDegree 3 ∧ G.CliqueFree 3 ∧
        ∃ x : ConfigSpace G, ‖malkounAmplitude G x‖ < 1 := by
  rcases exists_wagnerPath_zero with ⟨t₀, _, ht₀⟩
  exact ⟨8, wagnerGraph, instDecidableRelWagner, wagnerGraph_connected,
    wagnerGraph_threeVertexConnected, wagnerGraph_isRegularOfDegree_three,
    wagnerGraph_cliqueFree_three, wagnerPath t₀, by rw [ht₀, norm_zero]; norm_num⟩

/-- **Formal Disproof of Malkoun's Section 6 Real-Negativity Question on the triangle-free, 3-regular, 3-connected Wagner graph $M_8$.** -/
theorem disproof_malkoun_wagner_triangleFree_section_6 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ IsThreeVertexConnected G ∧ G.IsRegularOfDegree 3 ∧ G.CliqueFree 3 ∧
        ∃ x : ConfigSpace G, (malkounAmplitude G x).re < 0 ∧ (malkounAmplitude G x).im = 0 := by
  refine ⟨8, wagnerGraph, instDecidableRelWagner, wagnerGraph_connected,
    wagnerGraph_threeVertexConnected, wagnerGraph_isRegularOfDegree_three,
    wagnerGraph_cliqueFree_three, wagnerPath 1, ?_,
    planar_amplitude_im_eq_zero wagnerGraph (wagnerPath 1) (wagnerPath_planar 1)⟩
  rw [← wagnerAmpOne_eq]; exact wagnerAmpOne_re_neg

end WitnessAndDisproofs

end Matematyka.MalkounWagnerCounterexample
