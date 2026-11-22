import Matematyka.MalkounCounterexample

/-!
# Formal Disproof of Malkoun's Conjectures on a 7-Vertex 2-Vertex-Connected Planar Graph

We formalize the vertex-minimal (`n = 7`, `m = 11`) counterexample discovered in our scan:
`k4e2k3Graph` ($K_4 \cup_{2e} K_3$), formed from a $K_4$ block on $\{0, 1, 2, 3\}$ and a $K_3$
block on $\{4, 5, 6\}$ joined across the 2-edge cut $\{(2, 5), (3, 4)\}$.

Unlike the 8-vertex barbell in `Matematyka.MalkounCounterexample` (which has $\kappa = 1$),
`k4e2k3Graph` is **2-vertex-connected** (`IsTwoVertexConnected k4e2k3Graph`) as well as planar.

To certify the negative amplitude at the irrational-length planar configuration `n7Path 1`
without `Nat.sqrt` or `native_decide`, we verify a closed integer interval enclosure
(`IntIv` / `CIntIv`) at integer scale $S = 10^6$ using kernel `decide`, combine it with
an exact Gaussian-integer collinear evaluation (`+20736`) at `n7Path 0`, and apply
continuity and `intermediate_value_Icc'` along the straight-line homotopy `n7Path t`.
-/

namespace Matematyka.MalkounN7Counterexample

open Complex Matematyka.MalkounCounterexample

private lemma fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

/-! ## Part 1: The 7-Vertex 2-Vertex-Connected Graph `k4e2k3Graph` ($K_4 \cup_{2e} K_3$) -/

section GraphAndConnectivity

/-- Boolean adjacency predicate on `Fin 7` for `k4e2k3Graph` ($K_4 \cup_{2e} K_3$, $m = 11$). -/
def k4e2k3AdjBool (u v : Fin 7) : Bool :=
  (u != v) &&
    ((u.val ≤ 3 && v.val ≤ 3) ||
     (4 ≤ u.val && 4 ≤ v.val) ||
     (u.val == 2 && v.val == 5) || (u.val == 5 && v.val == 2) ||
     (u.val == 3 && v.val == 4) || (u.val == 4 && v.val == 3))

/-- The 7-vertex, 11-edge planar 2-vertex-connected graph $K_4 \cup_{2e} K_3$. -/
def k4e2k3Graph : SimpleGraph (Fin 7) where
  Adj u v := k4e2k3AdjBool u v = true
  symm := by
    have h : ∀ u v : Fin 7, k4e2k3AdjBool u v = true → k4e2k3AdjBool v u = true := by decide
    exact ⟨h⟩
  loopless := by
    have h : ∀ u : Fin 7, k4e2k3AdjBool u u ≠ true := by decide
    exact ⟨h⟩

instance instDecidableRelK4e2k3 : DecidableRel k4e2k3Graph.Adj := fun u v =>
  inferInstanceAs (Decidable (k4e2k3AdjBool u v = true))

theorem k4e2k3Graph_connected : k4e2k3Graph.Connected := by
  refine ⟨fun u v => ?_⟩
  have h0 : ∀ w : Fin 7, k4e2k3Graph.Reachable 0 w := by
    intro w
    fin_cases w
    · exact SimpleGraph.Reachable.refl 0
    · exact SimpleGraph.Adj.reachable (by decide)
    · exact SimpleGraph.Adj.reachable (by decide)
    · exact SimpleGraph.Adj.reachable (by decide)
    · exact (SimpleGraph.Adj.reachable (by decide : k4e2k3Graph.Adj 0 3)).trans
        (SimpleGraph.Adj.reachable (by decide : k4e2k3Graph.Adj 3 4))
    · exact (SimpleGraph.Adj.reachable (by decide : k4e2k3Graph.Adj 0 2)).trans
        (SimpleGraph.Adj.reachable (by decide : k4e2k3Graph.Adj 2 5))
    · exact (SimpleGraph.Adj.reachable (by decide : k4e2k3Graph.Adj 0 3)).trans
        ((SimpleGraph.Adj.reachable (by decide : k4e2k3Graph.Adj 3 4)).trans
          (SimpleGraph.Adj.reachable (by decide : k4e2k3Graph.Adj 4 6)))
  exact (h0 u).symm.trans (h0 v)

/-- A finite simple graph on `Fin n` is **2-vertex-connected** ($\kappa(G) \ge 2$) when
$n \ge 3$, $G$ is connected, and deleting any single vertex leaves a connected graph. -/
def IsTwoVertexConnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  3 ≤ n ∧ G.Connected ∧ ∀ c : Fin n, (G.induce {x : Fin n | x ≠ c}).Connected

private lemma reach_induce_step {n : ℕ} {G : SimpleGraph (Fin n)} {c u v w : Fin n}
    {hu : u ≠ c} {hv : v ≠ c} {hw : w ≠ c}
    (huv : G.Adj u v)
    (hrest : (G.induce {x : Fin n | x ≠ c}).Reachable ⟨v, hv⟩ ⟨w, hw⟩) :
    (G.induce {x : Fin n | x ≠ c}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ :=
  have hadj : (G.induce {x : Fin n | x ≠ c}).Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
  hadj.reachable.trans hrest

private lemma reach_induce_adj {n : ℕ} {G : SimpleGraph (Fin n)} {c u v : Fin n}
    {hu : u ≠ c} {hv : v ≠ c} (huv : G.Adj u v) :
    (G.induce {x : Fin n | x ≠ c}).Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  have hadj : (G.induce {x : Fin n | x ≠ c}).Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
  hadj.reachable

private lemma k4e2k3_induce_reach_anchor (c : Fin 7) :
    ∃ a : {x : Fin 7 | x ≠ c},
      ∀ u : {x : Fin 7 | x ≠ c}, (k4e2k3Graph.induce {x : Fin 7 | x ≠ c}).Reachable u a := by
  by_cases hc0 : c = 0
  · subst hc0
    refine ⟨⟨1, by decide⟩, ?_⟩
    rintro ⟨u, hu⟩
    fin_cases u
    · exact absurd rfl hu
    · exact SimpleGraph.Reachable.refl _
    · exact reach_induce_adj (by decide : k4e2k3Graph.Adj 2 1)
    · exact reach_induce_adj (by decide : k4e2k3Graph.Adj 3 1)
    · exact reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 4 3)
        (reach_induce_adj (by decide : k4e2k3Graph.Adj 3 1))
    · exact reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 5 2)
        (reach_induce_adj (by decide : k4e2k3Graph.Adj 2 1))
    · exact reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 6 4)
        (reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 4 3)
          (reach_induce_adj (by decide : k4e2k3Graph.Adj 3 1)))
  · refine ⟨⟨0, Ne.symm hc0⟩, ?_⟩
    rintro ⟨u, hu⟩
    fin_cases u
    · exact SimpleGraph.Reachable.refl _
    · exact reach_induce_adj (by decide : k4e2k3Graph.Adj 1 0)
    · exact reach_induce_adj (by decide : k4e2k3Graph.Adj 2 0)
    · exact reach_induce_adj (by decide : k4e2k3Graph.Adj 3 0)
    · by_cases hc3 : c = 3
      · subst hc3
        exact reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 4 5)
          (reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 5 2)
            (reach_induce_adj (by decide : k4e2k3Graph.Adj 2 0)))
      · exact reach_induce_step (hv := Ne.symm hc3) (by decide : k4e2k3Graph.Adj 4 3)
          (reach_induce_adj (by decide : k4e2k3Graph.Adj 3 0))
    · by_cases hc2 : c = 2
      · subst hc2
        exact reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 5 4)
          (reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 4 3)
            (reach_induce_adj (by decide : k4e2k3Graph.Adj 3 0)))
      · exact reach_induce_step (hv := Ne.symm hc2) (by decide : k4e2k3Graph.Adj 5 2)
          (reach_induce_adj (by decide : k4e2k3Graph.Adj 2 0))
    · by_cases hc4 : c = 4
      · subst hc4
        exact reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 6 5)
          (reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 5 2)
            (reach_induce_adj (by decide : k4e2k3Graph.Adj 2 0)))
      · by_cases hc3 : c = 3
        · subst hc3
          exact reach_induce_step (hv := Ne.symm hc4) (by decide : k4e2k3Graph.Adj 6 4)
            (reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 4 5)
              (reach_induce_step (hv := by decide) (by decide : k4e2k3Graph.Adj 5 2)
                (reach_induce_adj (by decide : k4e2k3Graph.Adj 2 0))))
        · exact reach_induce_step (hv := Ne.symm hc4) (by decide : k4e2k3Graph.Adj 6 4)
            (reach_induce_step (hv := Ne.symm hc3) (by decide : k4e2k3Graph.Adj 4 3)
              (reach_induce_adj (by decide : k4e2k3Graph.Adj 3 0)))

theorem k4e2k3Graph_twoVertexConnected : IsTwoVertexConnected k4e2k3Graph := by
  refine ⟨by decide, k4e2k3Graph_connected, fun c => ?_⟩
  rcases k4e2k3_induce_reach_anchor c with ⟨a, ha⟩
  have : Nonempty {x : Fin 7 | x ≠ c} := ⟨a⟩
  exact ⟨fun u v => (ha u).trans (ha v).symm⟩

end GraphAndConnectivity

/-! ## Part 2: 2-Edge-Cut Dicke Factorization for `k4e2k3Graph` -/

section K4E2K3Combinatorics

/-- Vertex degrees of `k4e2k3Graph`: `3, 3, 4, 4, 3, 3, 2`. -/
@[reducible] def k4e2k3Deg : Fin 7 → ℕ
  | 0 => 3
  | 1 => 3
  | 2 => 4
  | 3 => 4
  | 4 => 3
  | 5 => 3
  | 6 => 2

/-- Ordered neighbor list of each vertex of `k4e2k3Graph`.
Vertices `2` and `3` place their bridge neighbor last (index `3`);
vertices `4` and `5` place their bridge neighbor first (index `0`). -/
def k4e2k3Nbr : ∀ u : Fin 7, Fin (k4e2k3Deg u) → Fin 7
  | 0 => fun j => match j with | 0 => 1 | 1 => 2 | 2 => 3
  | 1 => fun j => match j with | 0 => 0 | 1 => 2 | 2 => 3
  | 2 => fun j => match j with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5
  | 3 => fun j => match j with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4
  | 4 => fun j => match j with | 0 => 3 | 1 => 5 | 2 => 6
  | 5 => fun j => match j with | 0 => 2 | 1 => 4 | 2 => 6
  | 6 => fun j => match j with | 0 => 4 | 1 => 5

def k4e2k3NbrIdx : ∀ u : Fin 7, Fin 7 → Fin (k4e2k3Deg u)
  | 0 => fun w => if w.val == 1 then 0 else if w.val == 2 then 1 else 2
  | 1 => fun w => if w.val == 0 then 0 else if w.val == 2 then 1 else 2
  | 2 => fun w => if w.val == 0 then 0 else if w.val == 1 then 1 else if w.val == 3 then 2 else 3
  | 3 => fun w => if w.val == 0 then 0 else if w.val == 1 then 1 else if w.val == 2 then 2 else 3
  | 4 => fun w => if w.val == 3 then 0 else if w.val == 5 then 1 else 2
  | 5 => fun w => if w.val == 2 then 0 else if w.val == 4 then 1 else 2
  | 6 => fun w => if w.val == 4 then 0 else 1

private lemma k4e2k3Nbr_adj : ∀ u : Fin 7, ∀ j : Fin (k4e2k3Deg u),
    k4e2k3Graph.Adj u (k4e2k3Nbr u j) := by
  intro u; fin_cases u <;> decide

private lemma k4e2k3Nbr_left_inv : ∀ u : Fin 7, ∀ j : Fin (k4e2k3Deg u),
    k4e2k3NbrIdx u (k4e2k3Nbr u j) = j := by
  intro u; fin_cases u <;> decide

private lemma k4e2k3Nbr_right_inv : ∀ u w : Fin 7,
    k4e2k3Graph.Adj u w → k4e2k3Nbr u (k4e2k3NbrIdx u w) = w := by
  intro u; fin_cases u <;> decide

private def k4e2k3NbrEquiv (u : Fin 7) :
    Fin (k4e2k3Deg u) ≃ { w : Fin 7 // k4e2k3Graph.Adj u w } where
  toFun j := ⟨k4e2k3Nbr u j, k4e2k3Nbr_adj u j⟩
  invFun w := k4e2k3NbrIdx u w.1
  left_inv j := k4e2k3Nbr_left_inv u j
  right_inv w := Subtype.ext (k4e2k3Nbr_right_inv u w.1 w.2)

abbrev LeftPerm7 := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)
abbrev RightPerm7 := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)

private def matchFin7 {P : Fin 7 → Type*}
    (x0 : P 0) (x1 : P 1) (x2 : P 2) (x3 : P 3)
    (x4 : P 4) (x5 : P 5) (x6 : P 6) : ∀ u : Fin 7, P u
  | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3
  | 4 => x4 | 5 => x5 | 6 => x6

private def leftRightPi7Equiv :
    LeftPerm7 × RightPerm7 ≃ (∀ u : Fin 7, Equiv.Perm (Fin (k4e2k3Deg u))) where
  toFun p := matchFin7 p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2.1 p.2.2.2
  invFun f := ((f 0, f 1, f 2, f 3), (f 4, f 5, f 6))
  left_inv _ := rfl
  right_inv f := funext fun u => by fin_cases u <;> rfl

private def k4e2k3SourcePermEquiv : LeftPerm7 × RightPerm7 ≃ SourcePerm k4e2k3Graph :=
  leftRightPi7Equiv.trans (Equiv.piCongrRight fun u => Equiv.permCongr (k4e2k3NbrEquiv u))

/-- Left-block $K_4$ edges (`6` edges). -/
def leftEdgePairs7 : Fin 6 → Fin 7 × Fin 7 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- 2-edge cut bridging $\{0,1,2,3\}$ to $\{4,5,6\}$. -/
def bridgeEdgePairs7 : Fin 2 → Fin 7 × Fin 7 :=
  ![(2, 5), (3, 4)]

/-- Right-block $K_3$ edges (`3` edges). -/
def rightEdgePairs7 : Fin 3 → Fin 7 × Fin 7 :=
  ![(4, 5), (4, 6), (5, 6)]

private lemma leftEdgePairs7_ok : ∀ i : Fin 6,
    k4e2k3Graph.Adj (leftEdgePairs7 i).1 (leftEdgePairs7 i).2 ∧
      (leftEdgePairs7 i).1 < (leftEdgePairs7 i).2 := by
  decide

private lemma bridgeEdgePairs7_ok : ∀ i : Fin 2,
    k4e2k3Graph.Adj (bridgeEdgePairs7 i).1 (bridgeEdgePairs7 i).2 ∧
      (bridgeEdgePairs7 i).1 < (bridgeEdgePairs7 i).2 := by
  decide

private lemma rightEdgePairs7_ok : ∀ i : Fin 3,
    k4e2k3Graph.Adj (rightEdgePairs7 i).1 (rightEdgePairs7 i).2 ∧
      (rightEdgePairs7 i).1 < (rightEdgePairs7 i).2 := by
  decide

private def k4e2k3OriToFun : Fin 6 ⊕ Fin 2 ⊕ Fin 3 → OriEdge k4e2k3Graph
  | .inl i => ⟨leftEdgePairs7 i, leftEdgePairs7_ok i⟩
  | .inr (.inl i) => ⟨bridgeEdgePairs7 i, bridgeEdgePairs7_ok i⟩
  | .inr (.inr i) => ⟨rightEdgePairs7 i, rightEdgePairs7_ok i⟩

private def k4e2k3OriInvFun (e : OriEdge k4e2k3Graph) : Fin 6 ⊕ Fin 2 ⊕ Fin 3 :=
  match e.1 with
  | (0, 1) => .inl 0 | (0, 2) => .inl 1 | (0, 3) => .inl 2
  | (1, 2) => .inl 3 | (1, 3) => .inl 4 | (2, 3) => .inl 5
  | (2, 5) => .inr (.inl 0) | (3, 4) => .inr (.inl 1)
  | (4, 5) => .inr (.inr 0) | (4, 6) => .inr (.inr 1) | (5, 6) => .inr (.inr 2)
  | _ => .inl 0

private def k4e2k3OriEquiv : (Fin 6 ⊕ Fin 2 ⊕ Fin 3) ≃ OriEdge k4e2k3Graph where
  toFun := k4e2k3OriToFun
  invFun := k4e2k3OriInvFun
  left_inv x := by
    rcases x with i | (i | i) <;> [fin_cases i <;> rfl; fin_cases i <;> rfl; fin_cases i <;> rfl]
  right_inv e := Subtype.ext (by
    rcases e with ⟨⟨u, v⟩, hadj, hlt⟩
    fin_cases u <;> fin_cases v <;> first | rfl | (exfalso; revert hadj hlt; decide))

private def leftU7 (L : LeftPerm7) : Fin 6 → Fin 7 × Fin 7
  | 0 => (0, k4e2k3Nbr 0 (L.1 0))
  | 1 => (0, k4e2k3Nbr 0 (L.1 1))
  | 2 => (0, k4e2k3Nbr 0 (L.1 2))
  | 3 => (1, k4e2k3Nbr 1 (L.2.1 1))
  | 4 => (1, k4e2k3Nbr 1 (L.2.1 2))
  | 5 => (2, k4e2k3Nbr 2 (L.2.2.1 2))

private def leftV7 (L : LeftPerm7) : Fin 6 → Fin 7 × Fin 7
  | 0 => (1, k4e2k3Nbr 1 (L.2.1 0))
  | 1 => (2, k4e2k3Nbr 2 (L.2.2.1 0))
  | 2 => (3, k4e2k3Nbr 3 (L.2.2.2 0))
  | 3 => (2, k4e2k3Nbr 2 (L.2.2.1 1))
  | 4 => (3, k4e2k3Nbr 3 (L.2.2.2 1))
  | 5 => (3, k4e2k3Nbr 3 (L.2.2.2 2))

private def rightU7 (R : RightPerm7) : Fin 3 → Fin 7 × Fin 7
  | 0 => (4, k4e2k3Nbr 4 (R.1 1))
  | 1 => (4, k4e2k3Nbr 4 (R.1 2))
  | 2 => (5, k4e2k3Nbr 5 (R.2.1 2))

private def rightV7 (R : RightPerm7) : Fin 3 → Fin 7 × Fin 7
  | 0 => (5, k4e2k3Nbr 5 (R.2.1 1))
  | 1 => (6, k4e2k3Nbr 6 (R.2.2 0))
  | 2 => (6, k4e2k3Nbr 6 (R.2.2 1))

private lemma k4e2k3SourcePermEquiv_apply (L : LeftPerm7) (R : RightPerm7) (u w : Fin 7)
    (hw : k4e2k3Graph.Adj u w) :
    (k4e2k3SourcePermEquiv (L, R) u ⟨w, hw⟩).1 =
      k4e2k3Nbr u ((leftRightPi7Equiv (L, R) u) (k4e2k3NbrIdx u w)) := by
  simp [k4e2k3SourcePermEquiv, Equiv.piCongrRight_apply, Equiv.permCongr_apply, k4e2k3NbrEquiv]

private lemma k4e2k3_term_edge (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (L : LeftPerm7) (R : RightPerm7)
    (e : OriEdge k4e2k3Graph) :
    let σ := k4e2k3SourcePermEquiv (L, R)
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ e.1.1 (k4e2k3Nbr e.1.1 ((leftRightPi7Equiv (L, R) e.1.1) (k4e2k3NbrIdx e.1.1 e.1.2))))
            (ψ e.1.2 (k4e2k3Nbr e.1.2 ((leftRightPi7Equiv (L, R) e.1.2) (k4e2k3NbrIdx e.1.2 e.1.1)))) := by
  intro σ
  rw [k4e2k3SourcePermEquiv_apply, k4e2k3SourcePermEquiv_apply]

private lemma k4e2k3_term_bridge0 (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (L : LeftPerm7) (R : RightPerm7) :
    let σ := k4e2k3SourcePermEquiv (L, R)
    let e := k4e2k3OriEquiv (.inr (.inl 0))
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)
          (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ 2 (k4e2k3Nbr 2 (L.2.2.1 3))) (ψ 5 (k4e2k3Nbr 5 (R.2.1 0))) := by
  dsimp only
  rw [k4e2k3_term_edge]
  rfl

private lemma k4e2k3_term_bridge1 (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (L : LeftPerm7) (R : RightPerm7) :
    let σ := k4e2k3SourcePermEquiv (L, R)
    let e := k4e2k3OriEquiv (.inr (.inl 1))
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)
          (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ 3 (k4e2k3Nbr 3 (L.2.2.2 3))) (ψ 4 (k4e2k3Nbr 4 (R.1 0))) := by
  dsimp only
  rw [k4e2k3_term_edge]
  rfl

private lemma k4e2k3_term_left (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (L : LeftPerm7) (R : RightPerm7)
    (i : Fin 6) :
    let σ := k4e2k3SourcePermEquiv (L, R)
    let e := k4e2k3OriEquiv (.inl i)
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)
          (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2) := by
  dsimp only
  rw [k4e2k3_term_edge]
  fin_cases i <;> rfl

private lemma k4e2k3_term_right (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (L : LeftPerm7) (R : RightPerm7)
    (i : Fin 3) :
    let σ := k4e2k3SourcePermEquiv (L, R)
    let e := k4e2k3OriEquiv (.inr (.inr i))
    omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1)
          (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1) =
      omega (ψ (rightU7 R i).1 (rightU7 R i).2) (ψ (rightV7 R i).1 (rightV7 R i).2) := by
  dsimp only
  rw [k4e2k3_term_edge]
  fin_cases i <;> rfl

private def sgnBitC (b : Fin 2) : ℂ := if b = 0 then 1 else -1

noncomputable def leftHalf7Val (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (β₂ β₃ : Fin 2) : ℂ :=
  ∑ L : LeftPerm7,
    ψ 2 (k4e2k3Nbr 2 (L.2.2.1 3)) β₂ *
    ψ 3 (k4e2k3Nbr 3 (L.2.2.2 3)) β₃ *
    ∏ i : Fin 6, omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2)

noncomputable def rightHalf7Val (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (γ₂ γ₃ : Fin 2) : ℂ :=
  ∑ R : RightPerm7,
    ψ 5 (k4e2k3Nbr 5 (R.2.1 0)) γ₂ *
    ψ 4 (k4e2k3Nbr 4 (R.1 0)) γ₃ *
    ∏ i : Fin 3, omega (ψ (rightU7 R i).1 (rightU7 R i).2) (ψ (rightV7 R i).1 (rightV7 R i).2)

private def invBit (b : Fin 2) : Fin 2 := 1 - b

private lemma omega_eq_sub_bit (a b : Fin 2 → ℂ) :
    omega a b = (a 0 * b (invBit 0)) - (a 1 * b (invBit 1)) := by
  have h0 : invBit 0 = 1 := by decide
  have h1 : invBit 1 = 0 := by decide
  simp [omega, h0, h1]

theorem malkounNum_k4e2k3_bridge (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) :
    malkounNum k4e2k3Graph ψ =
      ∑ β₂ : Fin 2, ∑ β₃ : Fin 2,
        sgnBitC β₂ * sgnBitC β₃ *
          leftHalf7Val ψ β₂ β₃ * rightHalf7Val ψ (invBit β₂) (invBit β₃) := by
  unfold malkounNum
  rw [← Fintype.sum_equiv k4e2k3SourcePermEquiv
    (fun p => ∏ e : OriEdge k4e2k3Graph,
      omega (ψ e.1.1 ((k4e2k3SourcePermEquiv p) e.1.1 ⟨e.1.2, e.2.1⟩).1)
            (ψ e.1.2 ((k4e2k3SourcePermEquiv p) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
    (fun σ => ∏ e : OriEdge k4e2k3Graph,
      omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
    (fun _ => rfl)]
  have hs0 : sgnBitC 0 = 1 := by simp [sgnBitC]
  have hs1 : sgnBitC 1 = -1 := by
    have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    simp [sgnBitC, h10]
  have hinv0 : invBit 0 = 1 := by decide
  have hinv1 : invBit 1 = 0 := by decide
  have hprod : ∀ p : LeftPerm7 × RightPerm7,
      (∏ e : OriEdge k4e2k3Graph,
        omega (ψ e.1.1 ((k4e2k3SourcePermEquiv p) e.1.1 ⟨e.1.2, e.2.1⟩).1)
              (ψ e.1.2 ((k4e2k3SourcePermEquiv p) e.1.2 ⟨e.1.1, e.2.1.symm⟩).1)) =
      ∑ β₂ : Fin 2, ∑ β₃ : Fin 2,
        sgnBitC β₂ * sgnBitC β₃ *
        (ψ 2 (k4e2k3Nbr 2 (p.1.2.2.1 3)) β₂ *
          ψ 3 (k4e2k3Nbr 3 (p.1.2.2.2 3)) β₃ *
          ∏ i : Fin 6, omega (ψ (leftU7 p.1 i).1 (leftU7 p.1 i).2) (ψ (leftV7 p.1 i).1 (leftV7 p.1 i).2)) *
        (ψ 5 (k4e2k3Nbr 5 (p.2.2.1 0)) (invBit β₂) *
          ψ 4 (k4e2k3Nbr 4 (p.2.1 0)) (invBit β₃) *
          ∏ i : Fin 3, omega (ψ (rightU7 p.2 i).1 (rightU7 p.2 i).2) (ψ (rightV7 p.2 i).1 (rightV7 p.2 i).2)) := by
    rintro ⟨L, R⟩
    let σ := k4e2k3SourcePermEquiv (L, R)
    rw [← Fintype.prod_equiv k4e2k3OriEquiv
      (fun x => omega (ψ (k4e2k3OriEquiv x).1.1 (σ (k4e2k3OriEquiv x).1.1 ⟨(k4e2k3OriEquiv x).1.2, (k4e2k3OriEquiv x).2.1⟩).1)
                      (ψ (k4e2k3OriEquiv x).1.2 (σ (k4e2k3OriEquiv x).1.2 ⟨(k4e2k3OriEquiv x).1.1, (k4e2k3OriEquiv x).2.1.symm⟩).1))
      (fun e => omega (ψ e.1.1 (σ e.1.1 ⟨e.1.2, e.2.1⟩).1) (ψ e.1.2 (σ e.1.2 ⟨e.1.1, e.2.1.symm⟩).1))
      (fun _ => rfl)]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_two]
    have hl : (∏ i : Fin 6,
        omega (ψ (k4e2k3OriEquiv (.inl i)).1.1 (σ (k4e2k3OriEquiv (.inl i)).1.1 ⟨(k4e2k3OriEquiv (.inl i)).1.2, (k4e2k3OriEquiv (.inl i)).2.1⟩).1)
              (ψ (k4e2k3OriEquiv (.inl i)).1.2 (σ (k4e2k3OriEquiv (.inl i)).1.2 ⟨(k4e2k3OriEquiv (.inl i)).1.1, (k4e2k3OriEquiv (.inl i)).2.1.symm⟩).1)) =
        ∏ i : Fin 6, omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2) :=
      Finset.prod_congr rfl fun i _ => k4e2k3_term_left ψ L R i
    have hr : (∏ i : Fin 3,
        omega (ψ (k4e2k3OriEquiv (.inr (.inr i))).1.1 (σ (k4e2k3OriEquiv (.inr (.inr i))).1.1 ⟨(k4e2k3OriEquiv (.inr (.inr i))).1.2, (k4e2k3OriEquiv (.inr (.inr i))).2.1⟩).1)
              (ψ (k4e2k3OriEquiv (.inr (.inr i))).1.2 (σ (k4e2k3OriEquiv (.inr (.inr i))).1.2 ⟨(k4e2k3OriEquiv (.inr (.inr i))).1.1, (k4e2k3OriEquiv (.inr (.inr i))).2.1.symm⟩).1)) =
        ∏ i : Fin 3, omega (ψ (rightU7 R i).1 (rightU7 R i).2) (ψ (rightV7 R i).1 (rightV7 R i).2) :=
      Finset.prod_congr rfl fun i _ => k4e2k3_term_right ψ L R i
    have hb0 :
        omega (ψ (k4e2k3OriEquiv (.inr (.inl 0))).1.1 (σ (k4e2k3OriEquiv (.inr (.inl 0))).1.1 ⟨(k4e2k3OriEquiv (.inr (.inl 0))).1.2, (k4e2k3OriEquiv (.inr (.inl 0))).2.1⟩).1)
              (ψ (k4e2k3OriEquiv (.inr (.inl 0))).1.2 (σ (k4e2k3OriEquiv (.inr (.inl 0))).1.2 ⟨(k4e2k3OriEquiv (.inr (.inl 0))).1.1, (k4e2k3OriEquiv (.inr (.inl 0))).2.1.symm⟩).1) =
        omega (ψ 2 (k4e2k3Nbr 2 (L.2.2.1 3))) (ψ 5 (k4e2k3Nbr 5 (R.2.1 0))) :=
      k4e2k3_term_bridge0 ψ L R
    have hb1 :
        omega (ψ (k4e2k3OriEquiv (.inr (.inl 1))).1.1 (σ (k4e2k3OriEquiv (.inr (.inl 1))).1.1 ⟨(k4e2k3OriEquiv (.inr (.inl 1))).1.2, (k4e2k3OriEquiv (.inr (.inl 1))).2.1⟩).1)
              (ψ (k4e2k3OriEquiv (.inr (.inl 1))).1.2 (σ (k4e2k3OriEquiv (.inr (.inl 1))).1.2 ⟨(k4e2k3OriEquiv (.inr (.inl 1))).1.1, (k4e2k3OriEquiv (.inr (.inl 1))).2.1.symm⟩).1) =
        omega (ψ 3 (k4e2k3Nbr 3 (L.2.2.2 3))) (ψ 4 (k4e2k3Nbr 4 (R.1 0))) :=
      k4e2k3_term_bridge1 ψ L R
    rw [hl, hr, hb0, hb1]
    simp only [Fin.sum_univ_two, hs0, hs1, hinv0, hinv1, omega]
    ring
  simp_rw [hprod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β₃ _ => ?_
  rw [Fintype.sum_prod_type]
  calc
    (∑ L : LeftPerm7, ∑ R : RightPerm7,
      sgnBitC β₂ * sgnBitC β₃ *
      (ψ 2 (k4e2k3Nbr 2 (L.2.2.1 3)) β₂ *
        ψ 3 (k4e2k3Nbr 3 (L.2.2.2 3)) β₃ *
        ∏ i : Fin 6, omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2)) *
      (ψ 5 (k4e2k3Nbr 5 (R.2.1 0)) (invBit β₂) *
        ψ 4 (k4e2k3Nbr 4 (R.1 0)) (invBit β₃) *
        ∏ i : Fin 3, omega (ψ (rightU7 R i).1 (rightU7 R i).2) (ψ (rightV7 R i).1 (rightV7 R i).2)))
        = ∑ L : LeftPerm7,
            (sgnBitC β₂ * sgnBitC β₃ *
              (ψ 2 (k4e2k3Nbr 2 (L.2.2.1 3)) β₂ *
                ψ 3 (k4e2k3Nbr 3 (L.2.2.2 3)) β₃ *
                ∏ i : Fin 6, omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2))) *
              rightHalf7Val ψ (invBit β₂) (invBit β₃) := by
          refine Finset.sum_congr rfl fun L _ => ?_
          rw [rightHalf7Val, Finset.mul_sum]
    _ = (∑ L : LeftPerm7,
          sgnBitC β₂ * sgnBitC β₃ *
            (ψ 2 (k4e2k3Nbr 2 (L.2.2.1 3)) β₂ *
              ψ 3 (k4e2k3Nbr 3 (L.2.2.2 3)) β₃ *
              ∏ i : Fin 6, omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2))) *
          rightHalf7Val ψ (invBit β₂) (invBit β₃) := (Finset.sum_mul _ _ _).symm
    _ = (sgnBitC β₂ * sgnBitC β₃ * leftHalf7Val ψ β₂ β₃) * rightHalf7Val ψ (invBit β₂) (invBit β₃) := by
          rw [leftHalf7Val, Finset.mul_sum]
    _ = sgnBitC β₂ * sgnBitC β₃ * leftHalf7Val ψ β₂ β₃ * rightHalf7Val ψ (invBit β₂) (invBit β₃) := by
          ring

private def sgn6C (b : Fin 6 → Fin 2) : ℂ :=
  ∏ i : Fin 6, (if b i = 0 then (1 : ℂ) else -1)

private def sgn3C (b : Fin 3 → Fin 2) : ℂ :=
  ∏ i : Fin 3, (if b i = 0 then (1 : ℂ) else -1)

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

private lemma sum_prod3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (s : ℂ) (fa : A → ℂ) (fb : B → ℂ) (fc : C → ℂ) :
    (∑ p : A × B × C, s * fa p.1 * fb p.2.1 * fc p.2.2) =
      s * (∑ a, fa a) * (∑ b, fb b) * (∑ c, fc c) := by
  rw [Fintype.sum_prod_type]
  calc (∑ a : A, ∑ q : B × C, s * fa a * fb q.1 * fc q.2)
      = ∑ a : A, ∑ b : B, ∑ c : C, s * fa a * fb b * fc c :=
          Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _
    _ = ∑ a : A, ∑ b : B, s * fa a * fb b * ∑ c : C, fc c :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ a : A, (s * fa a * ∑ b : B, fb b) * ∑ c : C, fc c := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          exact (Finset.mul_sum _ _ _).symm
    _ = s * (∑ a : A, fa a) * (∑ b : B, fb b) * ∑ c : C, fc c := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact (Finset.mul_sum _ _ _).symm

lemma leftHalf7Val_eq_sumBits (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (β₂ β₃ : Fin 2) :
    leftHalf7Val ψ β₂ β₃ = sumBits 6 fun b =>
      sgn6C b *
      vSumC 3 (fun j => ψ 0 (k4e2k3Nbr 0 j)) ![b 0, b 1, b 2] *
      vSumC 3 (fun j => ψ 1 (k4e2k3Nbr 1 j)) ![invBit (b 0), b 3, b 4] *
      vSumC 4 (fun j => ψ 2 (k4e2k3Nbr 2 j)) ![invBit (b 1), invBit (b 3), b 5, β₂] *
      vSumC 4 (fun j => ψ 3 (k4e2k3Nbr 3 j)) ![invBit (b 2), invBit (b 4), invBit (b 5), β₃] := by
  rw [← sum_bitFun_eq_sumBits 6]
  unfold leftHalf7Val
  have hexp : ∀ L : LeftPerm7,
      (ψ 2 (k4e2k3Nbr 2 (L.2.2.1 3)) β₂ *
        ψ 3 (k4e2k3Nbr 3 (L.2.2.2 3)) β₃ *
        ∏ i : Fin 6, omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2)) =
      ∑ b : Fin 6 → Fin 2,
        sgn6C b *
        (∏ j : Fin 3, ψ 0 (k4e2k3Nbr 0 (L.1 j)) (![b 0, b 1, b 2] j)) *
        (∏ j : Fin 3, ψ 1 (k4e2k3Nbr 1 (L.2.1 j)) (![invBit (b 0), b 3, b 4] j)) *
        (∏ j : Fin 4, ψ 2 (k4e2k3Nbr 2 (L.2.2.1 j)) (![invBit (b 1), invBit (b 3), b 5, β₂] j)) *
        (∏ j : Fin 4, ψ 3 (k4e2k3Nbr 3 (L.2.2.2 j)) (![invBit (b 2), invBit (b 4), invBit (b 5), β₃] j)) := by
    intro L
    have homega : ∀ i : Fin 6,
        omega (ψ (leftU7 L i).1 (leftU7 L i).2) (ψ (leftV7 L i).1 (leftV7 L i).2) =
        (ψ (leftU7 L i).1 (leftU7 L i).2 0 * ψ (leftV7 L i).1 (leftV7 L i).2 (invBit 0)) -
        (ψ (leftU7 L i).1 (leftU7 L i).2 1 * ψ (leftV7 L i).1 (leftV7 L i).2 (invBit 1)) :=
      fun i => omega_eq_sub_bit _ _
    simp_rw [homega]
    rw [prod_fin2_sub_eq_sumBits 6
      (fun i bit => ψ (leftU7 L i).1 (leftU7 L i).2 bit * ψ (leftV7 L i).1 (leftV7 L i).2 (invBit bit))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [sgn6C, Fin.prod_univ_six, Fin.prod_univ_three, Fin.prod_univ_four,
      leftU7, leftV7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfac := sum_prod4 (sgn6C b)
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 0 (k4e2k3Nbr 0 (a j)) (![b 0, b 1, b 2] j))
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 1 (k4e2k3Nbr 1 (a j)) (![invBit (b 0), b 3, b 4] j))
    (fun a : Equiv.Perm (Fin 4) => ∏ j : Fin 4, ψ 2 (k4e2k3Nbr 2 (a j)) (![invBit (b 1), invBit (b 3), b 5, β₂] j))
    (fun a : Equiv.Perm (Fin 4) => ∏ j : Fin 4, ψ 3 (k4e2k3Nbr 3 (a j)) (![invBit (b 2), invBit (b 4), invBit (b 5), β₃] j))
  rw [hfac,
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 0 (k4e2k3Nbr 0 j)) ![b 0, b 1, b 2],
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 1 (k4e2k3Nbr 1 j)) ![invBit (b 0), b 3, b 4],
    perm_sigma_sum_eq_dicke 4 (fun j => ψ 2 (k4e2k3Nbr 2 j)) ![invBit (b 1), invBit (b 3), b 5, β₂],
    perm_sigma_sum_eq_dicke 4 (fun j => ψ 3 (k4e2k3Nbr 3 j)) ![invBit (b 2), invBit (b 4), invBit (b 5), β₃]]
  simp only [vSumC]

lemma rightHalf7Val_eq_sumBits (ψ : Fin 7 → Fin 7 → Fin 2 → ℂ) (γ₂ γ₃ : Fin 2) :
    rightHalf7Val ψ γ₂ γ₃ = sumBits 3 fun r =>
      sgn3C r *
      vSumC 3 (fun j => ψ 4 (k4e2k3Nbr 4 j)) ![γ₃, r 0, r 1] *
      vSumC 3 (fun j => ψ 5 (k4e2k3Nbr 5 j)) ![γ₂, invBit (r 0), r 2] *
      vSumC 2 (fun j => ψ 6 (k4e2k3Nbr 6 j)) ![invBit (r 1), invBit (r 2)] := by
  rw [← sum_bitFun_eq_sumBits 3]
  unfold rightHalf7Val
  have hexp : ∀ R : RightPerm7,
      (ψ 5 (k4e2k3Nbr 5 (R.2.1 0)) γ₂ *
        ψ 4 (k4e2k3Nbr 4 (R.1 0)) γ₃ *
        ∏ i : Fin 3, omega (ψ (rightU7 R i).1 (rightU7 R i).2) (ψ (rightV7 R i).1 (rightV7 R i).2)) =
      ∑ r : Fin 3 → Fin 2,
        sgn3C r *
        (∏ j : Fin 3, ψ 4 (k4e2k3Nbr 4 (R.1 j)) (![γ₃, r 0, r 1] j)) *
        (∏ j : Fin 3, ψ 5 (k4e2k3Nbr 5 (R.2.1 j)) (![γ₂, invBit (r 0), r 2] j)) *
        (∏ j : Fin 2, ψ 6 (k4e2k3Nbr 6 (R.2.2 j)) (![invBit (r 1), invBit (r 2)] j)) := by
    intro R
    have homega : ∀ i : Fin 3,
        omega (ψ (rightU7 R i).1 (rightU7 R i).2) (ψ (rightV7 R i).1 (rightV7 R i).2) =
        (ψ (rightU7 R i).1 (rightU7 R i).2 0 * ψ (rightV7 R i).1 (rightV7 R i).2 (invBit 0)) -
        (ψ (rightU7 R i).1 (rightU7 R i).2 1 * ψ (rightV7 R i).1 (rightV7 R i).2 (invBit 1)) :=
      fun i => omega_eq_sub_bit _ _
    simp_rw [homega]
    rw [prod_fin2_sub_eq_sumBits 3
      (fun i bit => ψ (rightU7 R i).1 (rightU7 R i).2 bit * ψ (rightV7 R i).1 (rightV7 R i).2 (invBit bit))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [sgn3C, Fin.prod_univ_three, Fin.prod_univ_two,
      rightU7, rightV7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hfac := sum_prod3 (sgn3C r)
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 4 (k4e2k3Nbr 4 (a j)) (![γ₃, r 0, r 1] j))
    (fun a : Equiv.Perm (Fin 3) => ∏ j : Fin 3, ψ 5 (k4e2k3Nbr 5 (a j)) (![γ₂, invBit (r 0), r 2] j))
    (fun a : Equiv.Perm (Fin 2) => ∏ j : Fin 2, ψ 6 (k4e2k3Nbr 6 (a j)) (![invBit (r 1), invBit (r 2)] j))
  rw [hfac,
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 4 (k4e2k3Nbr 4 j)) ![γ₃, r 0, r 1],
    perm_sigma_sum_eq_dicke 3 (fun j => ψ 5 (k4e2k3Nbr 5 j)) ![γ₂, invBit (r 0), r 2],
    perm_sigma_sum_eq_dicke 2 (fun j => ψ 6 (k4e2k3Nbr 6 j)) ![invBit (r 1), invBit (r 2)]]
  simp only [vSumC]

/-! ### Exact `GI` Evaluator and $t = 0$ Collinear Certificate -/

private lemma invBit_val (b : Fin 2) : (invBit b).val = invBitNat b := by
  fin_cases b <;> rfl

private lemma bitSum2_eq (a b : Fin 2) :
    bitSum ![a, b] = a.val + b.val := by
  simp [bitSum, Fin.sum_univ_two]

private lemma bitSum3_eq (a b c : Fin 2) :
    bitSum ![a, b, c] = a.val + b.val + c.val := by
  simp [bitSum, Fin.sum_univ_three, add_assoc]

private lemma bitSum4_eq (a b c d : Fin 2) :
    bitSum ![a, b, c, d] = a.val + b.val + c.val + d.val := by
  simp [bitSum, Fin.sum_univ_four, add_assoc]

def vTab2GI (M : Fin 2 → Fin 2 → GI) : ℕ → GI
  | 0 => GI.ofInt 2 * GI.dickePolyCoeffGI M 0
  | 1 => GI.dickePolyCoeffGI M 1
  | _ => GI.ofInt 2 * GI.dickePolyCoeffGI M 2

private lemma toC_vTab2GI (M : Fin 2 → Fin 2 → GI) (c : Fin 2 → Fin 2) :
    GI.toC (vTab2GI M (bitSum c)) = vSumC 2 (fun i k => GI.toC (M i k)) c := by
  have hle : bitSum c ≤ 2 := bitSum_le c
  rcases h0 : bitSum c with _ | _ | _ | w
  all_goals
    simp only [vTab2GI, vSumC, h0, GI.toC_mul, GI.toC_ofInt, GI.toC_dickePolyCoeffGI]
  all_goals
    first | (dsimp; norm_num) | omega

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

def sgn3GI (r : Fin 3 → Fin 2) : GI :=
  let s (x : Fin 2) : ℤ := if x = 0 then 1 else -1
  GI.ofInt (s (r 0) * s (r 1) * s (r 2))

private lemma toC_sgn3GI (r : Fin 3 → Fin 2) : GI.toC (sgn3GI r) = sgn3C r := by
  simp only [sgn3GI, sgn3C, GI.toC_ofInt, Fin.prod_univ_three]
  push_cast
  rfl

private lemma toC_sgn6GI' (b : Fin 6 → Fin 2) : GI.toC (sgn6GI b) = sgn6C b := by
  simp only [sgn6GI, sgn6C, GI.toC_ofInt, Fin.prod_univ_six]
  push_cast
  rfl

def leftHalf7GI (ψ : Fin 7 → Fin 7 → Fin 2 → GI) (β₂ β₃ : Fin 2) : GI :=
  let t0 := vTab3GI (fun j => ψ 0 (k4e2k3Nbr 0 j))
  let t1 := vTab3GI (fun j => ψ 1 (k4e2k3Nbr 1 j))
  let t2 := vTab4GI (fun j => ψ 2 (k4e2k3Nbr 2 j))
  let t3 := vTab4GI (fun j => ψ 3 (k4e2k3Nbr 3 j))
  sumBits 6 fun b =>
    sgn6GI b *
    t0 ((b 0).val + (b 1).val + (b 2).val) *
    t1 (invBitNat (b 0) + (b 3).val + (b 4).val) *
    t2 (invBitNat (b 1) + invBitNat (b 3) + (b 5).val + β₂.val) *
    t3 (invBitNat (b 2) + invBitNat (b 4) + invBitNat (b 5) + β₃.val)

def rightHalf7GI (ψ : Fin 7 → Fin 7 → Fin 2 → GI) (γ₂ γ₃ : Fin 2) : GI :=
  let t4 := vTab3GI (fun j => ψ 4 (k4e2k3Nbr 4 j))
  let t5 := vTab3GI (fun j => ψ 5 (k4e2k3Nbr 5 j))
  let t6 := vTab2GI (fun j => ψ 6 (k4e2k3Nbr 6 j))
  sumBits 3 fun r =>
    sgn3GI r *
    t4 (γ₃.val + (r 0).val + (r 1).val) *
    t5 (γ₂.val + invBitNat (r 0) + (r 2).val) *
    t6 (invBitNat (r 1) + invBitNat (r 2))

def prod2GI (g : Fin 2 → GI) : GI := g 0 * g 1

def prod3GI (g : Fin 3 → GI) : GI := g 0 * g 1 * g 2

private lemma toC_prod2GI (g : Fin 2 → GI) : GI.toC (prod2GI g) = ∏ i : Fin 2, GI.toC (g i) := by
  rw [Fin.prod_univ_two]
  simp [prod2GI]

private lemma toC_prod3GI (g : Fin 3 → GI) : GI.toC (prod3GI g) = ∏ i : Fin 3, GI.toC (g i) := by
  rw [Fin.prod_univ_three]
  simp [prod3GI]

private lemma toC_prod6GI' (g : Fin 6 → GI) : GI.toC (prod6GI g) = ∏ i : Fin 6, GI.toC (g i) := by
  rw [Fin.prod_univ_six]; simp [prod6GI]

private def sgnBitGI (b : Fin 2) : GI := GI.ofInt (if b = 0 then 1 else -1)

private lemma toC_sgnBitGI (b : Fin 2) : GI.toC (sgnBitGI b) = sgnBitC b := by
  fin_cases b <;> simp [sgnBitGI, sgnBitC]

def k4e2k3NumGI (ψ : Fin 7 → Fin 7 → Fin 2 → GI) : GI :=
  sgnBitGI 0 * sgnBitGI 0 * leftHalf7GI ψ 0 0 * rightHalf7GI ψ 1 1 +
  sgnBitGI 0 * sgnBitGI 1 * leftHalf7GI ψ 0 1 * rightHalf7GI ψ 1 0 +
  sgnBitGI 1 * sgnBitGI 0 * leftHalf7GI ψ 1 0 * rightHalf7GI ψ 0 1 +
  sgnBitGI 1 * sgnBitGI 1 * leftHalf7GI ψ 1 1 * rightHalf7GI ψ 0 0

def k4e2k3DenGI (ψ : Fin 7 → Fin 7 → Fin 2 → GI) : GI :=
  prod6GI (fun i => omegaGI (ψ (leftEdgePairs7 i).1 (leftEdgePairs7 i).2)
                            (ψ (leftEdgePairs7 i).2 (leftEdgePairs7 i).1)) *
  prod2GI (fun i => omegaGI (ψ (bridgeEdgePairs7 i).1 (bridgeEdgePairs7 i).2)
                            (ψ (bridgeEdgePairs7 i).2 (bridgeEdgePairs7 i).1)) *
  prod3GI (fun i => omegaGI (ψ (rightEdgePairs7 i).1 (rightEdgePairs7 i).2)
                            (ψ (rightEdgePairs7 i).2 (rightEdgePairs7 i).1))

private lemma sumBits_congr {R : Type*} [Add R] :
    ∀ (m : ℕ) {f g : (Fin m → Fin 2) → R}, (∀ b, f b = g b) → sumBits m f = sumBits m g
  | 0, _, _, h => h Fin.elim0
  | m + 1, _, _, h => by
      simp only [sumBits]
      rw [sumBits_congr m (fun f => h (Fin.cons 0 f)),
          sumBits_congr m (fun f => h (Fin.cons 1 f))]

theorem malkounNum_k4e2k3_giToC (ψ : Fin 7 → Fin 7 → Fin 2 → GI) :
    GI.toC (k4e2k3NumGI ψ) = malkounNum k4e2k3Graph (fun u v k => GI.toC (ψ u v k)) := by
  have hl : ∀ β₂ β₃,
      GI.toC (leftHalf7GI ψ β₂ β₃) = leftHalf7Val (fun u v k => GI.toC (ψ u v k)) β₂ β₃ := by
    intro β₂ β₃
    rw [leftHalf7Val_eq_sumBits, leftHalf7GI, GI.toC_sumBits]
    refine sumBits_congr 6 fun b => ?_
    simp only [GI.toC_mul, toC_sgn6GI']
    rw [← bitSum3_eq, ← invBit_val (b 0), ← bitSum3_eq,
        ← invBit_val (b 1), ← invBit_val (b 3), ← bitSum4_eq,
        ← invBit_val (b 2), ← invBit_val (b 4), ← invBit_val (b 5), ← bitSum4_eq]
    simp only [toC_vTab3GI, toC_vTab4GI]
  have hr : ∀ γ₂ γ₃,
      GI.toC (rightHalf7GI ψ γ₂ γ₃) = rightHalf7Val (fun u v k => GI.toC (ψ u v k)) γ₂ γ₃ := by
    intro γ₂ γ₃
    rw [rightHalf7Val_eq_sumBits, rightHalf7GI, GI.toC_sumBits]
    refine sumBits_congr 3 fun r => ?_
    simp only [GI.toC_mul, toC_sgn3GI]
    rw [← bitSum3_eq, ← invBit_val (r 0), ← bitSum3_eq,
        ← invBit_val (r 1), ← invBit_val (r 2), ← bitSum2_eq]
    simp only [toC_vTab3GI, toC_vTab2GI]
  rw [malkounNum_k4e2k3_bridge, k4e2k3NumGI]
  have hinv0 : invBit 0 = 1 := by decide
  have hinv1 : invBit 1 = 0 := by decide
  simp only [Fin.sum_univ_two, GI.toC_add, GI.toC_mul, toC_sgnBitGI, hinv0, hinv1, hl, hr]
  ring

theorem malkounDen_k4e2k3_giToC (ψ : Fin 7 → Fin 7 → Fin 2 → GI) :
    GI.toC (k4e2k3DenGI ψ) = malkounDen k4e2k3Graph (fun u v k => GI.toC (ψ u v k)) := by
  unfold malkounDen k4e2k3DenGI
  rw [← Fintype.prod_equiv k4e2k3OriEquiv
    (fun x => omega (fun k => GI.toC (ψ (k4e2k3OriEquiv x).1.1 (k4e2k3OriEquiv x).1.2 k))
                    (fun k => GI.toC (ψ (k4e2k3OriEquiv x).1.2 (k4e2k3OriEquiv x).1.1 k)))
    (fun e => omega (fun k => GI.toC (ψ e.1.1 e.1.2 k)) (fun k => GI.toC (ψ e.1.2 e.1.1 k)))
    (fun _ => rfl)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  have hleft :
      (∏ i : Fin 6,
        omega (fun k => GI.toC (ψ (k4e2k3OriEquiv (.inl i)).1.1 (k4e2k3OriEquiv (.inl i)).1.2 k))
              (fun k => GI.toC (ψ (k4e2k3OriEquiv (.inl i)).1.2 (k4e2k3OriEquiv (.inl i)).1.1 k))) =
      GI.toC (prod6GI fun i => omegaGI (ψ (leftEdgePairs7 i).1 (leftEdgePairs7 i).2)
                                       (ψ (leftEdgePairs7 i).2 (leftEdgePairs7 i).1)) := by
    rw [toC_prod6GI']
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [k4e2k3OriEquiv, k4e2k3OriToFun]
  have hmid :
      (∏ i : Fin 2,
        omega (fun k => GI.toC (ψ (k4e2k3OriEquiv (.inr (.inl i))).1.1 (k4e2k3OriEquiv (.inr (.inl i))).1.2 k))
              (fun k => GI.toC (ψ (k4e2k3OriEquiv (.inr (.inl i))).1.2 (k4e2k3OriEquiv (.inr (.inl i))).1.1 k))) =
      GI.toC (prod2GI fun i => omegaGI (ψ (bridgeEdgePairs7 i).1 (bridgeEdgePairs7 i).2)
                                       (ψ (bridgeEdgePairs7 i).2 (bridgeEdgePairs7 i).1)) := by
    rw [toC_prod2GI]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [k4e2k3OriEquiv, k4e2k3OriToFun]
  have hright :
      (∏ i : Fin 3,
        omega (fun k => GI.toC (ψ (k4e2k3OriEquiv (.inr (.inr i))).1.1 (k4e2k3OriEquiv (.inr (.inr i))).1.2 k))
              (fun k => GI.toC (ψ (k4e2k3OriEquiv (.inr (.inr i))).1.2 (k4e2k3OriEquiv (.inr (.inr i))).1.1 k))) =
      GI.toC (prod3GI fun i => omegaGI (ψ (rightEdgePairs7 i).1 (rightEdgePairs7 i).2)
                                       (ψ (rightEdgePairs7 i).2 (rightEdgePairs7 i).1)) := by
    rw [toC_prod3GI]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [k4e2k3OriEquiv, k4e2k3OriToFun]
  rw [hleft, hmid, hright, GI.toC_mul, GI.toC_mul, mul_assoc]

end K4E2K3Combinatorics

/-! ## Part 3: Integer Interval Arithmetic (`IntIv` / `CIntIv`) and $S = 10^6$ Certificate -/

section IntervalArithmetic

/-- Closed integer interval `[lo, hi]` enclosing real numbers. -/
structure IntIv where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

namespace IntIv

def zmin (x y : ℤ) : ℤ := if x ≤ y then x else y
def zmax (x y : ℤ) : ℤ := if x ≤ y then y else x

private lemma zmin_le_left (x y : ℤ) : zmin x y ≤ x := by unfold zmin; split_ifs <;> omega
private lemma zmin_le_right (x y : ℤ) : zmin x y ≤ y := by unfold zmin; split_ifs <;> omega
private lemma le_zmax_left (x y : ℤ) : x ≤ zmax x y := by unfold zmax; split_ifs <;> omega
private lemma le_zmax_right (x y : ℤ) : y ≤ zmax x y := by unfold zmax; split_ifs <;> omega

def Mem (a : IntIv) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

def zero : IntIv := ⟨0, 0⟩
def one : IntIv := ⟨1, 1⟩
def ofInt (z : ℤ) : IntIv := ⟨z, z⟩
def add (a b : IntIv) : IntIv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : IntIv) : IntIv := ⟨a.lo - b.hi, a.hi - b.lo⟩
def neg (a : IntIv) : IntIv := ⟨-a.hi, -a.lo⟩

def scaleInt (c : ℤ) (a : IntIv) : IntIv :=
  if 0 ≤ c then ⟨c * a.lo, c * a.hi⟩ else ⟨c * a.hi, c * a.lo⟩

def mul (a b : IntIv) : IntIv :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨zmin (zmin p1 p2) (zmin p3 p4), zmax (zmax p1 p2) (zmax p3 p4)⟩

lemma zero_mem : zero.Mem 0 := ⟨le_rfl, le_rfl⟩
lemma one_mem : one.Mem 1 := ⟨le_rfl, le_rfl⟩
lemma ofInt_mem (z : ℤ) : (ofInt z).Mem (z : ℝ) := ⟨le_rfl, le_rfl⟩

lemma add_mem {a b : IntIv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  refine ⟨?_, ?_⟩ <;> simp only [add, Int.cast_add] <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma sub_mem {a b : IntIv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.sub b).Mem (x - y) := by
  refine ⟨?_, ?_⟩ <;> simp only [sub, Int.cast_sub] <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma neg_mem {a : IntIv} {x : ℝ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  refine ⟨?_, ?_⟩ <;> simp only [neg, Int.cast_neg] <;> linarith [hx.1, hx.2]

lemma scaleInt_mem {c : ℤ} {a : IntIv} {x : ℝ} (hx : a.Mem x) :
    (a.scaleInt c).Mem ((c : ℝ) * x) := by
  unfold scaleInt Mem
  split_ifs with hc
  · have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    exact ⟨by push_cast; exact mul_le_mul_of_nonneg_left hx.1 hcR,
           by push_cast; exact mul_le_mul_of_nonneg_left hx.2 hcR⟩
  · have hcR : (c : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hc
    exact ⟨by push_cast; exact mul_le_mul_of_nonpos_left hx.2 hcR,
           by push_cast; exact mul_le_mul_of_nonpos_left hx.1 hcR⟩

private lemma mul_mem_bounds {c y l h : ℝ} (hy : l ≤ y ∧ y ≤ h) :
    min (c * l) (c * h) ≤ c * y ∧ c * y ≤ max (c * l) (c * h) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy.1 hc),
           le_trans (mul_le_mul_of_nonneg_left hy.2 hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy.2 hc),
           le_trans (mul_le_mul_of_nonpos_left hy.1 hc) (le_max_left _ _)⟩

lemma mul_mem {a b : IntIv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul b).Mem (x * y) := by
  have hyx := mul_mem_bounds (c := y) (y := x) hx
  have hal := mul_mem_bounds (c := (a.lo : ℝ)) (y := y) hy
  have hah := mul_mem_bounds (c := (a.hi : ℝ)) (y := y) hy
  have hcomm1 : y * (a.lo : ℝ) = (a.lo : ℝ) * y := mul_comm _ _
  have hcomm2 : y * (a.hi : ℝ) = (a.hi : ℝ) * y := mul_comm _ _
  have hcomm3 : y * x = x * y := mul_comm _ _
  rw [hcomm1, hcomm2, hcomm3] at hyx
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  have hp1 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.lo : ℝ) * (b.lo : ℝ) := by
    exact_mod_cast le_trans (zmin_le_left _ _) (zmin_le_left _ _)
  have hp2 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.lo : ℝ) * (b.hi : ℝ) := by
    exact_mod_cast le_trans (zmin_le_left _ _) (zmin_le_right _ _)
  have hp3 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.hi : ℝ) * (b.lo : ℝ) := by
    exact_mod_cast le_trans (zmin_le_right _ _) (zmin_le_left _ _)
  have hp4 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.hi : ℝ) * (b.hi : ℝ) := by
    exact_mod_cast le_trans (zmin_le_right _ _) (zmin_le_right _ _)
  have hq1 : (a.lo : ℝ) * (b.lo : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_left _ _) (le_zmax_left _ _)
  have hq2 : (a.lo : ℝ) * (b.hi : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_right _ _) (le_zmax_left _ _)
  have hq3 : (a.hi : ℝ) * (b.lo : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_left _ _) (le_zmax_right _ _)
  have hq4 : (a.hi : ℝ) * (b.hi : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_right _ _) (le_zmax_right _ _)
  refine ⟨?_, ?_⟩
  · exact le_trans (le_min (le_trans (le_min hp1 hp2) hal.1) (le_trans (le_min hp3 hp4) hah.1)) hyx.1
  · exact le_trans hyx.2 (max_le (le_trans hal.2 (max_le hq1 hq2)) (le_trans hah.2 (max_le hq3 hq4)))

end IntIv

/-- Rectangular interval in $\mathbb{C}$ enclosing real and imaginary parts separately. -/
structure CIntIv where
  re : IntIv
  im : IntIv
  deriving DecidableEq

namespace CIntIv

def Mem (a : CIntIv) (z : ℂ) : Prop := a.re.Mem z.re ∧ a.im.Mem z.im

def zero : CIntIv := ⟨IntIv.zero, IntIv.zero⟩
def one : CIntIv := ⟨IntIv.one, IntIv.zero⟩
def add (a b : CIntIv) : CIntIv := ⟨a.re.add b.re, a.im.add b.im⟩
def sub (a b : CIntIv) : CIntIv := ⟨a.re.sub b.re, a.im.sub b.im⟩
def scaleInt (c : ℤ) (a : CIntIv) : CIntIv := ⟨a.re.scaleInt c, a.im.scaleInt c⟩
def mul (a b : CIntIv) : CIntIv :=
  ⟨(a.re.mul b.re).sub (a.im.mul b.im), (a.re.mul b.im).add (a.im.mul b.re)⟩

instance : Zero CIntIv := ⟨zero⟩
instance : One CIntIv := ⟨one⟩
instance : Add CIntIv := ⟨add⟩
instance : Sub CIntIv := ⟨sub⟩
instance : Mul CIntIv := ⟨mul⟩

lemma zero_mem : zero.Mem 0 := ⟨IntIv.zero_mem, IntIv.zero_mem⟩
lemma one_mem : one.Mem 1 := ⟨IntIv.one_mem, IntIv.zero_mem⟩

lemma add_mem {a b : CIntIv} {w z : ℂ} (hw : a.Mem w) (hz : b.Mem z) :
    (a + b).Mem (w + z) :=
  ⟨IntIv.add_mem hw.1 hz.1, IntIv.add_mem hw.2 hz.2⟩

lemma sub_mem {a b : CIntIv} {w z : ℂ} (hw : a.Mem w) (hz : b.Mem z) :
    (a - b).Mem (w - z) :=
  ⟨IntIv.sub_mem hw.1 hz.1, IntIv.sub_mem hw.2 hz.2⟩

lemma scaleInt_mem {c : ℤ} {a : CIntIv} {z : ℂ} (hz : a.Mem z) :
    (a.scaleInt c).Mem (((c : ℤ) : ℂ) * z) := by
  have h1 : (((c : ℤ) : ℂ) * z).re = (c : ℝ) * z.re := by simp
  have h2 : (((c : ℤ) : ℂ) * z).im = (c : ℝ) * z.im := by simp
  exact ⟨h1 ▸ IntIv.scaleInt_mem hz.1, h2 ▸ IntIv.scaleInt_mem hz.2⟩

lemma mul_mem {a b : CIntIv} {w z : ℂ} (hw : a.Mem w) (hz : b.Mem z) :
    (a * b).Mem (w * z) := by
  have hre : (w * z).re = w.re * z.re - w.im * z.im := Complex.mul_re w z
  have him : (w * z).im = w.re * z.im + w.im * z.re := Complex.mul_im w z
  exact ⟨hre ▸ IntIv.sub_mem (IntIv.mul_mem hw.1 hz.1) (IntIv.mul_mem hw.2 hz.2),
         him ▸ IntIv.add_mem (IntIv.mul_mem hw.1 hz.2) (IntIv.mul_mem hw.2 hz.1)⟩

end CIntIv

def dickePolyCoeffCIntIv : ∀ {n : ℕ}, (Fin n → Fin 2 → CIntIv) → ℕ → CIntIv
  | 0, _, k => if k = 0 then CIntIv.one else CIntIv.zero
  | _ + 1, M, 0 => M 0 0 * dickePolyCoeffCIntIv (fun j => M j.succ) 0
  | _ + 1, M, k + 1 =>
      M 0 0 * dickePolyCoeffCIntIv (fun j => M j.succ) (k + 1) +
        M 0 1 * dickePolyCoeffCIntIv (fun j => M j.succ) k

lemma dickePolyCoeffCIntIv_mem :
    ∀ {n : ℕ} (M : Fin n → Fin 2 → CIntIv) (Mc : Fin n → Fin 2 → ℂ)
      (_hM : ∀ i k, (M i k).Mem (Mc i k)) (k : ℕ),
      (dickePolyCoeffCIntIv M k).Mem (dickePolyCoeff Mc k)
  | 0, _, _, _, k => by
      by_cases hk : k = 0 <;> simp [dickePolyCoeffCIntIv, dickePolyCoeff, hk, CIntIv.one_mem,
        CIntIv.zero_mem]
  | _ + 1, M, Mc, hM, 0 => by
      simp only [dickePolyCoeffCIntIv, dickePolyCoeff]
      exact CIntIv.mul_mem (hM 0 0)
        (dickePolyCoeffCIntIv_mem (fun j => M j.succ) (fun j => Mc j.succ) (fun j => hM j.succ) 0)
  | _ + 1, M, Mc, hM, k + 1 => by
      simp only [dickePolyCoeffCIntIv, dickePolyCoeff]
      exact CIntIv.add_mem
        (CIntIv.mul_mem (hM 0 0)
          (dickePolyCoeffCIntIv_mem (fun j => M j.succ) (fun j => Mc j.succ)
            (fun j => hM j.succ) (k + 1)))
        (CIntIv.mul_mem (hM 0 1)
          (dickePolyCoeffCIntIv_mem (fun j => M j.succ) (fun j => Mc j.succ)
            (fun j => hM j.succ) k))

/-- Precomputed vertex Dicke lookup table of size `≤ 4` so each vertex is evaluated once under `decide`. -/
structure VTabIv where
  v0 : CIntIv
  v1 : CIntIv
  v2 : CIntIv
  v3 : CIntIv
  v4 : CIntIv
  deriving DecidableEq

def VTabIv.get (t : VTabIv) : ℕ → CIntIv
  | 0 => t.v0
  | 1 => t.v1
  | 2 => t.v2
  | 3 => t.v3
  | _ => t.v4

def mkVTab2Iv (M : Fin 2 → Fin 2 → CIntIv) : VTabIv :=
  ⟨(dickePolyCoeffCIntIv M 0).scaleInt 2,
   dickePolyCoeffCIntIv M 1,
   (dickePolyCoeffCIntIv M 2).scaleInt 2,
   CIntIv.zero,
   CIntIv.zero⟩

def mkVTab3Iv (M : Fin 3 → Fin 2 → CIntIv) : VTabIv :=
  ⟨(dickePolyCoeffCIntIv M 0).scaleInt 6,
   (dickePolyCoeffCIntIv M 1).scaleInt 2,
   (dickePolyCoeffCIntIv M 2).scaleInt 2,
   (dickePolyCoeffCIntIv M 3).scaleInt 6,
   CIntIv.zero⟩

def mkVTab4Iv (M : Fin 4 → Fin 2 → CIntIv) : VTabIv :=
  ⟨(dickePolyCoeffCIntIv M 0).scaleInt 24,
   (dickePolyCoeffCIntIv M 1).scaleInt 6,
   (dickePolyCoeffCIntIv M 2).scaleInt 4,
   (dickePolyCoeffCIntIv M 3).scaleInt 6,
   (dickePolyCoeffCIntIv M 4).scaleInt 24⟩

private lemma mkVTab2Iv_mem (M : Fin 2 → Fin 2 → CIntIv) (Mc : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i k, (M i k).Mem (Mc i k)) (c : Fin 2 → Fin 2) :
    ((mkVTab2Iv M).get (bitSum c)).Mem (vSumC 2 Mc c) := by
  have hle : bitSum c ≤ 2 := bitSum_le c
  rcases h0 : bitSum c with _ | _ | _ | w
  all_goals simp only [VTabIv.get, mkVTab2Iv, vSumC, h0]
  · simpa using CIntIv.scaleInt_mem (c := 2) (dickePolyCoeffCIntIv_mem M Mc hM 0)
  · simpa using dickePolyCoeffCIntIv_mem M Mc hM 1
  · simpa using CIntIv.scaleInt_mem (c := 2) (dickePolyCoeffCIntIv_mem M Mc hM 2)
  · omega

private lemma mkVTab3Iv_mem (M : Fin 3 → Fin 2 → CIntIv) (Mc : Fin 3 → Fin 2 → ℂ)
    (hM : ∀ i k, (M i k).Mem (Mc i k)) (c : Fin 3 → Fin 2) :
    ((mkVTab3Iv M).get (bitSum c)).Mem (vSumC 3 Mc c) := by
  have hle : bitSum c ≤ 3 := bitSum_le c
  have hf6 : ((Nat.factorial 0 * Nat.factorial 3 : ℕ) : ℂ) = ((6 : ℤ) : ℂ) := by norm_num
  have hf6' : ((Nat.factorial 3 * Nat.factorial 0 : ℕ) : ℂ) = ((6 : ℤ) : ℂ) := by norm_num
  have hf2 : ((Nat.factorial 1 * Nat.factorial 2 : ℕ) : ℂ) = ((2 : ℤ) : ℂ) := by norm_num
  have hf2' : ((Nat.factorial 2 * Nat.factorial 1 : ℕ) : ℂ) = ((2 : ℤ) : ℂ) := by norm_num
  rcases h0 : bitSum c with _ | _ | _ | _ | w
  all_goals simp only [VTabIv.get, mkVTab3Iv, vSumC, h0]
  · rw [hf6]; exact CIntIv.scaleInt_mem (c := 6) (dickePolyCoeffCIntIv_mem M Mc hM 0)
  · rw [hf2]; exact CIntIv.scaleInt_mem (c := 2) (dickePolyCoeffCIntIv_mem M Mc hM 1)
  · rw [hf2']; exact CIntIv.scaleInt_mem (c := 2) (dickePolyCoeffCIntIv_mem M Mc hM 2)
  · rw [hf6']; exact CIntIv.scaleInt_mem (c := 6) (dickePolyCoeffCIntIv_mem M Mc hM 3)
  · omega

private lemma mkVTab4Iv_mem (M : Fin 4 → Fin 2 → CIntIv) (Mc : Fin 4 → Fin 2 → ℂ)
    (hM : ∀ i k, (M i k).Mem (Mc i k)) (c : Fin 4 → Fin 2) :
    ((mkVTab4Iv M).get (bitSum c)).Mem (vSumC 4 Mc c) := by
  have hle : bitSum c ≤ 4 := bitSum_le c
  have hf24 : ((Nat.factorial 0 * Nat.factorial 4 : ℕ) : ℂ) = ((24 : ℤ) : ℂ) := by norm_num
  have hf24' : ((Nat.factorial 4 * Nat.factorial 0 : ℕ) : ℂ) = ((24 : ℤ) : ℂ) := by norm_num
  have hf6 : ((Nat.factorial 1 * Nat.factorial 3 : ℕ) : ℂ) = ((6 : ℤ) : ℂ) := by norm_num
  have hf6' : ((Nat.factorial 3 * Nat.factorial 1 : ℕ) : ℂ) = ((6 : ℤ) : ℂ) := by norm_num
  have hf4 : ((Nat.factorial 2 * Nat.factorial 2 : ℕ) : ℂ) = ((4 : ℤ) : ℂ) := by norm_num
  rcases h0 : bitSum c with _ | _ | _ | _ | _ | w
  all_goals simp only [VTabIv.get, mkVTab4Iv, vSumC, h0]
  · rw [hf24]; exact CIntIv.scaleInt_mem (c := 24) (dickePolyCoeffCIntIv_mem M Mc hM 0)
  · rw [hf6]; exact CIntIv.scaleInt_mem (c := 6) (dickePolyCoeffCIntIv_mem M Mc hM 1)
  · rw [hf4]; exact CIntIv.scaleInt_mem (c := 4) (dickePolyCoeffCIntIv_mem M Mc hM 2)
  · rw [hf6']; exact CIntIv.scaleInt_mem (c := 6) (dickePolyCoeffCIntIv_mem M Mc hM 3)
  · rw [hf24']; exact CIntIv.scaleInt_mem (c := 24) (dickePolyCoeffCIntIv_mem M Mc hM 4)
  · omega

private def sgnIntBit (x : Fin 2) : ℤ := if x = 0 then 1 else -1

private lemma sgnIntBit_cast (x : Fin 2) : ((sgnIntBit x : ℤ) : ℂ) = if x = 0 then 1 else -1 := by
  fin_cases x <;> simp [sgnIntBit]

def sgnInt6 (b : Fin 6 → Fin 2) : ℤ :=
  sgnIntBit (b 0) * sgnIntBit (b 1) * sgnIntBit (b 2) *
    sgnIntBit (b 3) * sgnIntBit (b 4) * sgnIntBit (b 5)

def sgnInt3 (r : Fin 3 → Fin 2) : ℤ :=
  sgnIntBit (r 0) * sgnIntBit (r 1) * sgnIntBit (r 2)

private lemma sgnInt6_eq_sgn6C (b : Fin 6 → Fin 2) :
    ((sgnInt6 b : ℤ) : ℂ) = sgn6C b := by
  simp only [sgnInt6, sgn6C, Fin.prod_univ_six, Int.cast_mul, sgnIntBit_cast]

private lemma sgnInt3_eq_sgn3C (r : Fin 3 → Fin 2) :
    ((sgnInt3 r : ℤ) : ℂ) = sgn3C r := by
  simp only [sgnInt3, sgn3C, Fin.prod_univ_three, Int.cast_mul, sgnIntBit_cast]

private lemma sumBits_cintIv_mem :
    ∀ (m : ℕ) (f : (Fin m → Fin 2) → CIntIv) (fc : (Fin m → Fin 2) → ℂ),
      (∀ b, (f b).Mem (fc b)) →
      (sumBits m f).Mem (sumBits m fc)
  | 0, _, _, h => h Fin.elim0
  | m + 1, f, fc, h => by
      simp only [sumBits]
      exact CIntIv.add_mem
        (sumBits_cintIv_mem m (fun b => f (Fin.cons 0 b)) (fun b => fc (Fin.cons 0 b))
          (fun b => h _))
        (sumBits_cintIv_mem m (fun b => f (Fin.cons 1 b)) (fun b => fc (Fin.cons 1 b))
          (fun b => h _))

def leftHalf7TabsIv (t0 t1 t2 t3 : VTabIv) (β₂ β₃ : Fin 2) : CIntIv :=
  sumBits 6 fun b =>
    (t0.get ((b 0).val + (b 1).val + (b 2).val) *
      t1.get (invBitNat (b 0) + (b 3).val + (b 4).val) *
      t2.get (invBitNat (b 1) + invBitNat (b 3) + (b 5).val + β₂.val) *
      t3.get (invBitNat (b 2) + invBitNat (b 4) + invBitNat (b 5) + β₃.val)).scaleInt (sgnInt6 b)

def rightHalf7TabsIv (t4 t5 t6 : VTabIv) (γ₂ γ₃ : Fin 2) : CIntIv :=
  sumBits 3 fun r =>
    (t4.get (γ₃.val + (r 0).val + (r 1).val) *
      t5.get (γ₂.val + invBitNat (r 0) + (r 2).val) *
      t6.get (invBitNat (r 1) + invBitNat (r 2))).scaleInt (sgnInt3 r)

def k4e2k3NumIv (ψ : Fin 7 → Fin 7 → Fin 2 → CIntIv) : CIntIv :=
  let t0 := mkVTab3Iv (fun j => ψ 0 (k4e2k3Nbr 0 j))
  let t1 := mkVTab3Iv (fun j => ψ 1 (k4e2k3Nbr 1 j))
  let t2 := mkVTab4Iv (fun j => ψ 2 (k4e2k3Nbr 2 j))
  let t3 := mkVTab4Iv (fun j => ψ 3 (k4e2k3Nbr 3 j))
  let t4 := mkVTab3Iv (fun j => ψ 4 (k4e2k3Nbr 4 j))
  let t5 := mkVTab3Iv (fun j => ψ 5 (k4e2k3Nbr 5 j))
  let t6 := mkVTab2Iv (fun j => ψ 6 (k4e2k3Nbr 6 j))
  (leftHalf7TabsIv t0 t1 t2 t3 0 0 * rightHalf7TabsIv t4 t5 t6 1 1).scaleInt 1 +
  (leftHalf7TabsIv t0 t1 t2 t3 0 1 * rightHalf7TabsIv t4 t5 t6 1 0).scaleInt (-1) +
  (leftHalf7TabsIv t0 t1 t2 t3 1 0 * rightHalf7TabsIv t4 t5 t6 0 1).scaleInt (-1) +
  (leftHalf7TabsIv t0 t1 t2 t3 1 1 * rightHalf7TabsIv t4 t5 t6 0 0).scaleInt 1

def omegaIv (a b : Fin 2 → CIntIv) : CIntIv := a 0 * b 1 - a 1 * b 0

lemma omegaIv_mem {a b : Fin 2 → CIntIv} {ac bc : Fin 2 → ℂ}
    (ha : ∀ k, (a k).Mem (ac k)) (hb : ∀ k, (b k).Mem (bc k)) :
    (omegaIv a b).Mem (omega ac bc) :=
  CIntIv.sub_mem (CIntIv.mul_mem (ha 0) (hb 1)) (CIntIv.mul_mem (ha 1) (hb 0))

def prod2Iv (g : Fin 2 → CIntIv) : CIntIv := g 0 * g 1
def prod3Iv (g : Fin 3 → CIntIv) : CIntIv := g 0 * g 1 * g 2
def prod6Iv (g : Fin 6 → CIntIv) : CIntIv := g 0 * g 1 * g 2 * g 3 * g 4 * g 5

lemma prod2Iv_mem (g : Fin 2 → CIntIv) (gc : Fin 2 → ℂ) (hg : ∀ i, (g i).Mem (gc i)) :
    (prod2Iv g).Mem (∏ i : Fin 2, gc i) := by
  rw [Fin.prod_univ_two]; exact CIntIv.mul_mem (hg 0) (hg 1)

lemma prod3Iv_mem (g : Fin 3 → CIntIv) (gc : Fin 3 → ℂ) (hg : ∀ i, (g i).Mem (gc i)) :
    (prod3Iv g).Mem (∏ i : Fin 3, gc i) := by
  rw [Fin.prod_univ_three]; exact CIntIv.mul_mem (CIntIv.mul_mem (hg 0) (hg 1)) (hg 2)

lemma prod6Iv_mem (g : Fin 6 → CIntIv) (gc : Fin 6 → ℂ) (hg : ∀ i, (g i).Mem (gc i)) :
    (prod6Iv g).Mem (∏ i : Fin 6, gc i) := by
  rw [Fin.prod_univ_six]
  exact CIntIv.mul_mem (CIntIv.mul_mem (CIntIv.mul_mem (CIntIv.mul_mem
    (CIntIv.mul_mem (hg 0) (hg 1)) (hg 2)) (hg 3)) (hg 4)) (hg 5)

def k4e2k3DenIv (ψ : Fin 7 → Fin 7 → Fin 2 → CIntIv) : CIntIv :=
  prod6Iv (fun i => omegaIv (ψ (leftEdgePairs7 i).1 (leftEdgePairs7 i).2)
                            (ψ (leftEdgePairs7 i).2 (leftEdgePairs7 i).1)) *
  prod2Iv (fun i => omegaIv (ψ (bridgeEdgePairs7 i).1 (bridgeEdgePairs7 i).2)
                            (ψ (bridgeEdgePairs7 i).2 (bridgeEdgePairs7 i).1)) *
  prod3Iv (fun i => omegaIv (ψ (rightEdgePairs7 i).1 (rightEdgePairs7 i).2)
                            (ψ (rightEdgePairs7 i).2 (rightEdgePairs7 i).1))

theorem k4e2k3NumIv_mem (ψIv : Fin 7 → Fin 7 → Fin 2 → CIntIv)
    (ψC : Fin 7 → Fin 7 → Fin 2 → ℂ)
    (hψ : ∀ u v, k4e2k3Graph.Adj u v → ∀ k, (ψIv u v k).Mem (ψC u v k)) :
    (k4e2k3NumIv ψIv).Mem (malkounNum k4e2k3Graph ψC) := by
  have hl : ∀ β₂ β₃ : Fin 2,
      (leftHalf7TabsIv
        (mkVTab3Iv fun j => ψIv 0 (k4e2k3Nbr 0 j))
        (mkVTab3Iv fun j => ψIv 1 (k4e2k3Nbr 1 j))
        (mkVTab4Iv fun j => ψIv 2 (k4e2k3Nbr 2 j))
        (mkVTab4Iv fun j => ψIv 3 (k4e2k3Nbr 3 j)) β₂ β₃).Mem (leftHalf7Val ψC β₂ β₃) := by
    intro β₂ β₃
    rw [leftHalf7Val_eq_sumBits, leftHalf7TabsIv]
    refine sumBits_cintIv_mem 6 _ _ fun b => ?_
    have hv0 : ((mkVTab3Iv fun j => ψIv 0 (k4e2k3Nbr 0 j)).get
        ((b 0).val + (b 1).val + (b 2).val)).Mem
        (vSumC 3 (fun j => ψC 0 (k4e2k3Nbr 0 j)) ![b 0, b 1, b 2]) := by
      have h := mkVTab3Iv_mem _ (fun j => ψC 0 (k4e2k3Nbr 0 j))
        (fun j k => hψ 0 _ (k4e2k3Nbr_adj 0 j) k) ![b 0, b 1, b 2]
      rwa [bitSum3_eq] at h
    have hv1 : ((mkVTab3Iv fun j => ψIv 1 (k4e2k3Nbr 1 j)).get
        (invBitNat (b 0) + (b 3).val + (b 4).val)).Mem
        (vSumC 3 (fun j => ψC 1 (k4e2k3Nbr 1 j)) ![invBit (b 0), b 3, b 4]) := by
      have h := mkVTab3Iv_mem _ (fun j => ψC 1 (k4e2k3Nbr 1 j))
        (fun j k => hψ 1 _ (k4e2k3Nbr_adj 1 j) k) ![invBit (b 0), b 3, b 4]
      rwa [bitSum3_eq, invBit_val (b 0)] at h
    have hv2 : ((mkVTab4Iv fun j => ψIv 2 (k4e2k3Nbr 2 j)).get
        (invBitNat (b 1) + invBitNat (b 3) + (b 5).val + β₂.val)).Mem
        (vSumC 4 (fun j => ψC 2 (k4e2k3Nbr 2 j)) ![invBit (b 1), invBit (b 3), b 5, β₂]) := by
      have h := mkVTab4Iv_mem _ (fun j => ψC 2 (k4e2k3Nbr 2 j))
        (fun j k => hψ 2 _ (k4e2k3Nbr_adj 2 j) k) ![invBit (b 1), invBit (b 3), b 5, β₂]
      rwa [bitSum4_eq, invBit_val (b 1), invBit_val (b 3)] at h
    have hv3 : ((mkVTab4Iv fun j => ψIv 3 (k4e2k3Nbr 3 j)).get
        (invBitNat (b 2) + invBitNat (b 4) + invBitNat (b 5) + β₃.val)).Mem
        (vSumC 4 (fun j => ψC 3 (k4e2k3Nbr 3 j)) ![invBit (b 2), invBit (b 4), invBit (b 5), β₃]) := by
      have h := mkVTab4Iv_mem _ (fun j => ψC 3 (k4e2k3Nbr 3 j))
        (fun j k => hψ 3 _ (k4e2k3Nbr_adj 3 j) k) ![invBit (b 2), invBit (b 4), invBit (b 5), β₃]
      rwa [bitSum4_eq, invBit_val (b 2), invBit_val (b 4), invBit_val (b 5)] at h
    have hprod := CIntIv.mul_mem (CIntIv.mul_mem (CIntIv.mul_mem hv0 hv1) hv2) hv3
    have hsc := CIntIv.scaleInt_mem (c := sgnInt6 b) hprod
    rw [sgnInt6_eq_sgn6C b] at hsc
    simpa only [mul_assoc] using hsc
  have hr : ∀ γ₂ γ₃ : Fin 2,
      (rightHalf7TabsIv
        (mkVTab3Iv fun j => ψIv 4 (k4e2k3Nbr 4 j))
        (mkVTab3Iv fun j => ψIv 5 (k4e2k3Nbr 5 j))
        (mkVTab2Iv fun j => ψIv 6 (k4e2k3Nbr 6 j)) γ₂ γ₃).Mem (rightHalf7Val ψC γ₂ γ₃) := by
    intro γ₂ γ₃
    rw [rightHalf7Val_eq_sumBits, rightHalf7TabsIv]
    refine sumBits_cintIv_mem 3 _ _ fun r => ?_
    have hv4 : ((mkVTab3Iv fun j => ψIv 4 (k4e2k3Nbr 4 j)).get
        (γ₃.val + (r 0).val + (r 1).val)).Mem
        (vSumC 3 (fun j => ψC 4 (k4e2k3Nbr 4 j)) ![γ₃, r 0, r 1]) := by
      have h := mkVTab3Iv_mem _ (fun j => ψC 4 (k4e2k3Nbr 4 j))
        (fun j k => hψ 4 _ (k4e2k3Nbr_adj 4 j) k) ![γ₃, r 0, r 1]
      rwa [bitSum3_eq] at h
    have hv5 : ((mkVTab3Iv fun j => ψIv 5 (k4e2k3Nbr 5 j)).get
        (γ₂.val + invBitNat (r 0) + (r 2).val)).Mem
        (vSumC 3 (fun j => ψC 5 (k4e2k3Nbr 5 j)) ![γ₂, invBit (r 0), r 2]) := by
      have h := mkVTab3Iv_mem _ (fun j => ψC 5 (k4e2k3Nbr 5 j))
        (fun j k => hψ 5 _ (k4e2k3Nbr_adj 5 j) k) ![γ₂, invBit (r 0), r 2]
      rwa [bitSum3_eq, invBit_val (r 0)] at h
    have hv6 : ((mkVTab2Iv fun j => ψIv 6 (k4e2k3Nbr 6 j)).get
        (invBitNat (r 1) + invBitNat (r 2))).Mem
        (vSumC 2 (fun j => ψC 6 (k4e2k3Nbr 6 j)) ![invBit (r 1), invBit (r 2)]) := by
      have h := mkVTab2Iv_mem _ (fun j => ψC 6 (k4e2k3Nbr 6 j))
        (fun j k => hψ 6 _ (k4e2k3Nbr_adj 6 j) k) ![invBit (r 1), invBit (r 2)]
      rwa [bitSum2_eq, invBit_val (r 1), invBit_val (r 2)] at h
    have hprod := CIntIv.mul_mem (CIntIv.mul_mem hv4 hv5) hv6
    have hsc := CIntIv.scaleInt_mem (c := sgnInt3 r) hprod
    rw [sgnInt3_eq_sgn3C r] at hsc
    simpa only [mul_assoc] using hsc
  rw [malkounNum_k4e2k3_bridge, k4e2k3NumIv]
  have hs0 : sgnBitC 0 = 1 := by simp [sgnBitC]
  have hs1 : sgnBitC 1 = -1 := by
    have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    simp [sgnBitC, h10]
  have hinv0 : invBit 0 = 1 := by decide
  have hinv1 : invBit 1 = 0 := by decide
  simp only [Fin.sum_univ_two, hs0, hs1, hinv0, hinv1]
  have t00 := CIntIv.scaleInt_mem (c := 1) (CIntIv.mul_mem (hl 0 0) (hr 1 1))
  have t01 := CIntIv.scaleInt_mem (c := -1) (CIntIv.mul_mem (hl 0 1) (hr 1 0))
  have t10 := CIntIv.scaleInt_mem (c := -1) (CIntIv.mul_mem (hl 1 0) (hr 0 1))
  have t11 := CIntIv.scaleInt_mem (c := 1) (CIntIv.mul_mem (hl 1 1) (hr 0 0))
  have hsum := CIntIv.add_mem (CIntIv.add_mem (CIntIv.add_mem t00 t01) t10) t11
  have heq :
      ((1 : ℤ) : ℂ) * (leftHalf7Val ψC 0 0 * rightHalf7Val ψC 1 1) +
      ((-1 : ℤ) : ℂ) * (leftHalf7Val ψC 0 1 * rightHalf7Val ψC 1 0) +
      ((-1 : ℤ) : ℂ) * (leftHalf7Val ψC 1 0 * rightHalf7Val ψC 0 1) +
      ((1 : ℤ) : ℂ) * (leftHalf7Val ψC 1 1 * rightHalf7Val ψC 0 0) =
      ((1 : ℂ) * 1 * leftHalf7Val ψC 0 0 * rightHalf7Val ψC 1 1 +
        (1 : ℂ) * (-1) * leftHalf7Val ψC 0 1 * rightHalf7Val ψC 1 0) +
      ((-1 : ℂ) * 1 * leftHalf7Val ψC 1 0 * rightHalf7Val ψC 0 1 +
        (-1 : ℂ) * (-1) * leftHalf7Val ψC 1 1 * rightHalf7Val ψC 0 0) := by
    push_cast; ring
  exact heq ▸ hsum

theorem k4e2k3DenIv_mem (ψIv : Fin 7 → Fin 7 → Fin 2 → CIntIv)
    (ψC : Fin 7 → Fin 7 → Fin 2 → ℂ)
    (hψ : ∀ u v, k4e2k3Graph.Adj u v → ∀ k, (ψIv u v k).Mem (ψC u v k)) :
    (k4e2k3DenIv ψIv).Mem (malkounDen k4e2k3Graph ψC) := by
  unfold malkounDen k4e2k3DenIv
  rw [← Fintype.prod_equiv k4e2k3OriEquiv
    (fun x => omega (ψC (k4e2k3OriEquiv x).1.1 (k4e2k3OriEquiv x).1.2)
                    (ψC (k4e2k3OriEquiv x).1.2 (k4e2k3OriEquiv x).1.1))
    (fun e => omega (ψC e.1.1 e.1.2) (ψC e.1.2 e.1.1)) (fun _ => rfl)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  have hleft := prod6Iv_mem
    (fun i => omegaIv (ψIv (leftEdgePairs7 i).1 (leftEdgePairs7 i).2)
                      (ψIv (leftEdgePairs7 i).2 (leftEdgePairs7 i).1))
    (fun i => omega (ψC (k4e2k3OriEquiv (.inl i)).1.1 (k4e2k3OriEquiv (.inl i)).1.2)
                    (ψC (k4e2k3OriEquiv (.inl i)).1.2 (k4e2k3OriEquiv (.inl i)).1.1))
    fun i => by
      simpa [k4e2k3OriEquiv, k4e2k3OriToFun] using
        omegaIv_mem (hψ _ _ (leftEdgePairs7_ok i).1) (hψ _ _ (leftEdgePairs7_ok i).1.symm)
  have hmid := prod2Iv_mem
    (fun i => omegaIv (ψIv (bridgeEdgePairs7 i).1 (bridgeEdgePairs7 i).2)
                      (ψIv (bridgeEdgePairs7 i).2 (bridgeEdgePairs7 i).1))
    (fun i => omega (ψC (k4e2k3OriEquiv (.inr (.inl i))).1.1 (k4e2k3OriEquiv (.inr (.inl i))).1.2)
                    (ψC (k4e2k3OriEquiv (.inr (.inl i))).1.2 (k4e2k3OriEquiv (.inr (.inl i))).1.1))
    fun i => by
      simpa [k4e2k3OriEquiv, k4e2k3OriToFun] using
        omegaIv_mem (hψ _ _ (bridgeEdgePairs7_ok i).1) (hψ _ _ (bridgeEdgePairs7_ok i).1.symm)
  have hright := prod3Iv_mem
    (fun i => omegaIv (ψIv (rightEdgePairs7 i).1 (rightEdgePairs7 i).2)
                      (ψIv (rightEdgePairs7 i).2 (rightEdgePairs7 i).1))
    (fun i => omega (ψC (k4e2k3OriEquiv (.inr (.inr i))).1.1 (k4e2k3OriEquiv (.inr (.inr i))).1.2)
                    (ψC (k4e2k3OriEquiv (.inr (.inr i))).1.2 (k4e2k3OriEquiv (.inr (.inr i))).1.1))
    fun i => by
      simpa [k4e2k3OriEquiv, k4e2k3OriToFun] using
        omegaIv_mem (hψ _ _ (rightEdgePairs7_ok i).1) (hψ _ _ (rightEdgePairs7_ok i).1.symm)
  rw [← mul_assoc]
  exact CIntIv.mul_mem (CIntIv.mul_mem hleft hmid) hright

end IntervalArithmetic

/-! ## Part 4: Concrete 7-Vertex Witness, Exact $t=0$ & Interval $t=1$ Certificates -/

section WitnessAndCertificates

/-- Exact $x$-coordinates of the 7-vertex 2-connected planar counterexample (`K4_2e_K3_2conn_n7`). -/
def n7PtsX : Fin 7 → ℤ
  | 0 => 1 | 1 => -86 | 2 => -13 | 3 => -15 | 4 => -17 | 5 => 20 | 6 => 2

/-- Exact $y$-coordinates at $t = 1$ (scaled by $t$ along the straight-line homotopy). -/
def n7PtsY : Fin 7 → ℤ
  | 0 => -155 | 1 => -334 | 2 => -103 | 3 => -103 | 4 => -98 | 5 => -83 | 6 => 913

lemma n7PtsX_inj : Function.Injective n7PtsX := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp_all [n7PtsX]

def n7Scale : ℤ := 1000000

/-- Precomputed integer floor $\lfloor 10^6 \|p_v - p_u\| \rfloor$ at $t=1$ (avoids `Nat.sqrt`). -/
def distN7Lo (u v : Fin 7) : ℤ :=
  match u.val, v.val with
  | 0, 1 | 1, 0 => 199022611
  | 0, 2 | 2, 0 => 53851648
  | 0, 3 | 3, 0 => 54405882
  | 1, 2 | 2, 1 => 242260190
  | 1, 3 | 3, 1 => 241665057
  | 2, 3 | 3, 2 => 2000000
  | 2, 5 | 5, 2 => 38587562
  | 3, 4 | 4, 3 => 5385164
  | 4, 5 | 5, 4 => 39924929
  | 4, 6 | 6, 4 => 1011178520
  | 5, 6 | 6, 5 => 996162637
  | _, _ => 0

lemma distN7Lo_ok : ∀ u v : Fin 7, k4e2k3Graph.Adj u v →
    let dx := n7PtsX v - n7PtsX u
    let dy := n7PtsY v - n7PtsY u
    let lo := distN7Lo u v
    0 ≤ lo ∧ lo * lo ≤ n7Scale * n7Scale * (dx * dx + dy * dy) ∧
      n7Scale * n7Scale * (dx * dx + dy * dy) ≤ (lo + 1) * (lo + 1) := by
  decide

def spinorsN7ColGI (u v : Fin 7) : Fin 2 → GI :=
  let dx := n7PtsX v - n7PtsX u
  spinorFromInts ((dx.natAbs : ℤ)) dx 0

lemma spinorsN7ColGI_ok : ∀ u v : Fin 7, k4e2k3Graph.Adj u v →
    let dx := n7PtsX v - n7PtsX u
    let r : ℤ := (dx.natAbs : ℤ)
    let g := scaleFromInts r dx 0
    g ≠ 0 ∧ 0 ≤ r ∧ r * r = dx * dx ∧
    r = g * (spinorsN7ColGI u v 0).re ∧
    (spinorsN7ColGI u v 0).im = 0 ∧
    dx = g * (spinorsN7ColGI u v 1).re ∧
    0 = g * (spinorsN7ColGI u v 1).im := by
  decide

/-- Kernel-verified $t=0$ collinear numerator (`-42467328`). -/
theorem cert_n7_col_num : k4e2k3NumGI spinorsN7ColGI = GI.ofInt (-42467328) := by
  decide

/-- Kernel-verified $t=0$ collinear denominator (`-2048`, ratio $= +20736$). -/
theorem cert_n7_col_den : k4e2k3DenGI spinorsN7ColGI = GI.ofInt (-2048) := by
  decide

def spinorsN7Iv (u v : Fin 7) : Fin 2 → CIntIv
  | 0 => ⟨⟨distN7Lo u v, distN7Lo u v + 1⟩, IntIv.zero⟩
  | 1 => ⟨IntIv.ofInt (n7Scale * (n7PtsX v - n7PtsX u)),
          IntIv.ofInt (n7Scale * (n7PtsY v - n7PtsY u))⟩

def n7Tab0Val : VTabIv := ⟨⟨⟨3498634090015278902654976, 3498634236868536871962024⟩, ⟨0, 0⟩⟩, ⟨⟨-1155943587006814762000000, -1155943552982030216000000⟩, ⟨1191867360908444334000000, 1191867452320126848000000⟩⟩, ⟨⟨1310625739544000000000000, 1310625786956000000000000⟩, ⟨-1019320178648000000000000, -1019320146692000000000000⟩⟩, ⟨⟨-380880000000000000000000, -380880000000000000000000⟩, ⟨3477840000000000000000000, 3477840000000000000000000⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
def n7Tab1Val : VTabIv := ⟨⟨⟨69911654892038178802482780, 69911655821185515771814416⟩, ⟨0, 0⟩⟩, ⟨⟨24055673777827787942000000, 24055673989033338652000000⟩, ⟨65455579078097818794000000, 65455579658813415180000000⟩⟩, ⟨⟨-53134161102400000000000000, -53134160815592000000000000⟩, ⟨45164911751584000000000000, 45164911950052000000000000⟩⟩, ⟨⟨-60874452000000000000000000, -60874452000000000000000000⟩, ⟨-34379364000000000000000000, -34379364000000000000000000⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
def n7Tab2Val : VTabIv := ⟨⟨⟨24164044649414894312325120000000, 24164057906110352856116422198008⟩, ⟨0, 0⟩⟩, ⟨⟨-1124581258254719928426510000000, -1124576675140766245262748000000⟩, ⟨-8462461789533241568376678000000, -8462454040966254654627840000000⟩⟩, ⟨⟨-3437699287129884212000000000000, -3437694095985829104000000000000⟩, ⟨-881038647808907732000000000000, -881033362148576208000000000000⟩⟩, ⟨⟨-5056233272808000000000000000000, -5056229647512000000000000000000⟩, ⟨6878397048036000000000000000000, 6878400221364000000000000000000⟩⟩, ⟨⟨21185376000000000000000000000000, 21185376000000000000000000000000⟩, ⟨11622432000000000000000000000000, 11622432000000000000000000000000⟩⟩⟩
def n7Tab3Val : VTabIv := ⟨⟨⟨3398598689600003788556928000000, 3398601096534491442931292767440⟩, ⟨0, 0⟩⟩, ⟨⟨534344398190789174890164000000, 534345064715543044582440000000⟩, ⟨-835351708461971023159110000000, -835350193241909175865320000000⟩⟩, ⟨⟨228675657471952032000000000000, 228676679065107772000000000000⟩, ⟨-154770709237781400000000000000, -154769929457462008000000000000⟩⟩, ⟨⟨974110839216000000000000000000, 974111395476000000000000000000⟩, ⟨-185589372624000000000000000000, -185588797380000000000000000000⟩⟩, ⟨⟨1263168000000000000000000000000, 1263168000000000000000000000000⟩, ⟨-3155136000000000000000000000000, -3155136000000000000000000000000⟩⟩⟩
def n7Tab4Val : VTabIv := ⟨⟨⟨1304434186536700782678720, 1304434462726277548544700⟩, ⟨0, 0⟩⟩, ⟨⟨572611809600046568000000, 572611890751956630000000⟩, ⟨194383179314518932000000, 194383311939474050000000⟩⟩, ⟨⟨552246013294000000000000, 552246052702000000000000⟩, ⟨246360537582000000000000, 246360617630000000000000⟩⟩, ⟨⟨957216000000000000000000, 957216000000000000000000⟩, ⟨886164000000000000000000, 886164000000000000000000⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
def n7Tab5Val : VTabIv := ⟨⟨⟨9208162859552561733956556, 9208163338063462652798520⟩, ⟨0, 0⟩⟩, ⟨⟨-5524917716903022036000000, -5524917569123278102000000⟩, ⟨324832930573260936000000, 324833099686395430000000⟩⟩, ⟨⟨4677366548910000000000000, 4677366624192000000000000⟩, ⟨-2958457995542000000000000, -2958457853452000000000000⟩⟩, ⟨⟨-7479828000000000000000000, -7479828000000000000000000⟩, ⟨5370516000000000000000000, 5370516000000000000000000⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
def n7Tab6Val : VTabIv := ⟨⟨⟨2014596521921914480, 2014596525936596796⟩, ⟨0, 0⟩⟩, ⟨⟨-725876762000000, -725876725000000⟩, ⟨-2014254233934000000, -2014254231927000000⟩⟩, ⟨⟨-2014596000000000000, -2014596000000000000⟩, ⟨1452000000000000, 1452000000000000⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

private lemma cert_n7Tab0 : mkVTab3Iv (fun j => spinorsN7Iv 0 (k4e2k3Nbr 0 j)) = n7Tab0Val := by decide
private lemma cert_n7Tab1 : mkVTab3Iv (fun j => spinorsN7Iv 1 (k4e2k3Nbr 1 j)) = n7Tab1Val := by decide
private lemma cert_n7Tab2 : mkVTab4Iv (fun j => spinorsN7Iv 2 (k4e2k3Nbr 2 j)) = n7Tab2Val := by decide
private lemma cert_n7Tab3 : mkVTab4Iv (fun j => spinorsN7Iv 3 (k4e2k3Nbr 3 j)) = n7Tab3Val := by decide
private lemma cert_n7Tab4 : mkVTab3Iv (fun j => spinorsN7Iv 4 (k4e2k3Nbr 4 j)) = n7Tab4Val := by decide
private lemma cert_n7Tab5 : mkVTab3Iv (fun j => spinorsN7Iv 5 (k4e2k3Nbr 5 j)) = n7Tab5Val := by decide
private lemma cert_n7Tab6 : mkVTab2Iv (fun j => spinorsN7Iv 6 (k4e2k3Nbr 6 j)) = n7Tab6Val := by decide

def n7Left00Val : CIntIv := ⟨⟨-23177632770257199813366597938604495836584820013536554141452051421729043734912000000000000000000000000000000000000, -23177451773457307503616686471325053344408462051473193483961853108017595220864000000000000000000000000000000000000⟩, ⟨-2611970236344641558172700806266301880790196576667309563876862639469263729696000000000000000000000000000000000000, -2611794097342124895378497103493680827917012636595316788880351756359728343264000000000000000000000000000000000000⟩⟩
def n7Left01Val : CIntIv := ⟨⟨-39052597572499333810897935986026772894997708238480777154600946625312832000000000000000000000000000000000000000000, -39052434698513490223692947262396750240883598109764444378691246178266880000000000000000000000000000000000000000000⟩, ⟨16266215070160667607949071492267194790331985538101842164155856464907584000000000000000000000000000000000000000000, 16266374772932176543077217469157245159806947317488501139421839940937792000000000000000000000000000000000000000000⟩⟩
def n7Left10Val : CIntIv := ⟨⟨-13694271274985112459368111810024976527430460160421522843765279113821952000000000000000000000000000000000000000000, -13694118221938205118661185981563803202237815127457475337273835748921984000000000000000000000000000000000000000000⟩, ⟨40026905127069513904984676842983498109176185984880168412392158376863360000000000000000000000000000000000000000000, 40027078915550386343629286414900940218548298152057372621316849909288320000000000000000000000000000000000000000000⟩⟩
def n7Left11Val : CIntIv := ⟨⟨4112402176628912435144008457598530660818922484387288966880676864000000000000000000000000000000000000000000000000, 4112554729571132325384443968506000842113764186393981268007006080000000000000000000000000000000000000000000000000⟩, ⟨22958747710622694993509404843851467041261564797922411110624570368000000000000000000000000000000000000000000000000, 22958894627996306351084118084480606682347939301493917551652225216000000000000000000000000000000000000000000000000⟩⟩
def n7Right00Val : CIntIv := ⟨⟨50348938726626067309590309070048838996366477716796000000000000000000, 50348954035585306263379777758038685601112010819332000000000000000000⟩, ⟨5576089837812248833708815630484129480296768767084000000000000000000, 5576102782074514695106727417978974929411797709460000000000000000000⟩⟩
def n7Right01Val : CIntIv := ⟨⟨52669173460026667233593973109756504071948684000000000000000000000000, 52669182739553804937543772847265084585257684000000000000000000000000⟩, ⟨3406609311419610310853172056002060290390380000000000000000000000000, 3406618750282166374311346477435107023523604000000000000000000000000⟩⟩
def n7Right10Val : CIntIv := ⟨⟨-52687843339291268514427156946405096497612540000000000000000000000000, -52687827572267140553355967347036458595340152000000000000000000000000⟩, ⟨-3104692310137465067882139598568700222546148000000000000000000000000, -3104676098637340658863678487722410267577064000000000000000000000000⟩⟩
def n7Right11Val : CIntIv := ⟨⟨-50652408278193853141767698863441719044000000000000000000000000000000, -50652398078181571459947208230198386524000000000000000000000000000000⟩, ⟨-666016918251772001273568943006321692000000000000000000000000000000, -666006473902688991210432230764876932000000000000000000000000000000⟩⟩

private lemma cert_n7Left00 : leftHalf7TabsIv n7Tab0Val n7Tab1Val n7Tab2Val n7Tab3Val 0 0 = n7Left00Val := by decide
private lemma cert_n7Left01 : leftHalf7TabsIv n7Tab0Val n7Tab1Val n7Tab2Val n7Tab3Val 0 1 = n7Left01Val := by decide
private lemma cert_n7Left10 : leftHalf7TabsIv n7Tab0Val n7Tab1Val n7Tab2Val n7Tab3Val 1 0 = n7Left10Val := by decide
private lemma cert_n7Left11 : leftHalf7TabsIv n7Tab0Val n7Tab1Val n7Tab2Val n7Tab3Val 1 1 = n7Left11Val := by decide
private lemma cert_n7Right00 : rightHalf7TabsIv n7Tab4Val n7Tab5Val n7Tab6Val 0 0 = n7Right00Val := by decide
private lemma cert_n7Right01 : rightHalf7TabsIv n7Tab4Val n7Tab5Val n7Tab6Val 0 1 = n7Right01Val := by decide
private lemma cert_n7Right10 : rightHalf7TabsIv n7Tab4Val n7Tab5Val n7Tab6Val 1 0 = n7Right10Val := by decide
private lemma cert_n7Right11 : rightHalf7TabsIv n7Tab4Val n7Tab5Val n7Tab6Val 1 1 = n7Right11Val := by decide

def n7NumIv : CIntIv := k4e2k3NumIv spinorsN7Iv
def n7DenIv : CIntIv := k4e2k3DenIv spinorsN7Iv

def n7NumVal : CIntIv := ⟨⟨802510464437978872121760745597461246203667894751329957981881091935371404254679043415974386212406107450982142848000000000000000000000000000000000000000000000000000000000000000000, 840034477517556586859017874163494524488120869320048921184601823767689600933611366305174598171837060891435815040000000000000000000000000000000000000000000000000000000000000000000⟩, ⟨851885163492160552895124389853476014220479894821756947065743525473905307394362784746611266794008499745444133760000000000000000000000000000000000000000000000000000000000000000000, 889833797204491548800565637372498186707268933403186928435266817847173543639614946006979784115036405829304842368000000000000000000000000000000000000000000000000000000000000000000⟩⟩
def n7DenVal : CIntIv := ⟨⟨-457504486868138637675678401078707274332785055570643821072743485496096949481885249712591951787048791570540134400000000000000000000000000000000000000000000000000000000000000000000, -457503759334188582604529061808190709376944237920923131735736565627530889170199459585315924422548570417974476800000000000000000000000000000000000000000000000000000000000000000000⟩, ⟨-485043845139193233134019819858414263284387706478790438410160376098222900065357746783332323183349373463743692800000000000000000000000000000000000000000000000000000000000000000000, -485043112812196404106997729515212555914457581400545410191389894508685743354198561802824333769007104133903155200000000000000000000000000000000000000000000000000000000000000000000⟩⟩

theorem cert_n7_num_val : n7NumIv = n7NumVal := by
  dsimp only [n7NumIv, k4e2k3NumIv]
  rw [cert_n7Tab0, cert_n7Tab1, cert_n7Tab2, cert_n7Tab3, cert_n7Tab4, cert_n7Tab5, cert_n7Tab6]
  rw [cert_n7Left00, cert_n7Left01, cert_n7Left10, cert_n7Left11]
  rw [cert_n7Right00, cert_n7Right01, cert_n7Right10, cert_n7Right11]
  decide

theorem cert_n7_den_val : n7DenIv = n7DenVal := by
  decide

/-- Kernel-verified $t=1$ interval certificate at scale $S = 10^6$:
$\operatorname{Re}(\mathcal{N}\overline{\mathcal{D}}) \le \mathrm{hi} < 0$. -/
theorem cert_n7_dot_neg :
    ((n7NumVal.re.mul n7DenVal.re).add (n7NumVal.im.mul n7DenVal.im)).hi < 0 := by
  decide

end WitnessAndCertificates

/-! ## Part 5: Homotopy Path, Continuity, IVT, and Exported $n=7$ Biconnected Disproofs -/

section HomotopyDisproof

def n7Point (t : ℝ) (u : Fin 7) : Fin 3 → ℝ
  | 0 => (n7PtsX u : ℝ)
  | 1 => (n7PtsY u : ℝ) * t
  | 2 => 0

def n7Path (t : ℝ) : ConfigSpace k4e2k3Graph :=
  ⟨n7Point t, by
    intro u v huv h
    have hx : (n7PtsX u : ℝ) = (n7PtsX v : ℝ) := congr_fun h 0
    exact k4e2k3Graph.ne_of_adj huv (n7PtsX_inj (Int.cast_injective hx))⟩

lemma n7Path_planar (t : ℝ) (u : Fin 7) : (n7Path t).1 u 2 = 0 := rfl

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

private lemma match_collinear_n7 (u v : Fin 7) (dx r g : ℤ) (s : Fin 2 → GI)
    (hr_nn : 0 ≤ r)
    (hpt0 : n7Point 0 v 0 - n7Point 0 u 0 = (dx : ℝ))
    (hpt1 : n7Point 0 v 1 - n7Point 0 u 1 = 0)
    (hr_sq : r * r = dx * dx)
    (h0re : r = g * (s 0).re) (h0im : (s 0).im = 0)
    (h1re : dx = g * (s 1).re) (h1im : 0 = g * (s 1).im) :
    ∀ k : Fin 2, planarUnnormSpinor (n7Point 0 u) (n7Point 0 v) k =
      ((g : ℤ) : ℂ) * GI.toC (s k) := by
  have hr_R : (r : ℝ) ^ 2 = (n7Point 0 v 0 - n7Point 0 u 0) ^ 2 +
      (n7Point 0 v 1 - n7Point 0 u 1) ^ 2 +
      (n7Point 0 v 2 - n7Point 0 u 2) ^ 2 := by
    rw [hpt0, hpt1]
    simp only [n7Point, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    have hsq : (r : ℝ) * (r : ℝ) = (dx : ℝ) * (dx : ℝ) := by exact_mod_cast hr_sq
    linarith [sq (r : ℝ), sq (dx : ℝ)]
  have heuclid : euclidNorm (fun j => n7Point 0 v j - n7Point 0 u j) = (r : ℝ) := by
    rw [euclidNorm, ← hr_R]
    exact Real.sqrt_sq (by exact_mod_cast hr_nn)
  intro k
  rcases fin2_cases k with rfl | rfl
  · simp only [planarUnnormSpinor, heuclid, GI.toC, h0im, Int.cast_zero, mul_zero, add_zero]
    exact_mod_cast h0re
  · simp only [planarUnnormSpinor, hpt0, hpt1, Complex.ofReal_zero, mul_zero, add_zero, GI.toC]
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.add_re, Complex.I_re, zero_mul, Complex.I_im, mul_zero, sub_self, add_zero,
        sub_zero]
      exact_mod_cast h1re
    · simp only [Complex.ofReal_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        Complex.add_im, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_add, add_zero]
      exact_mod_cast h1im

theorem malkounAmplitude_n7Path_zero :
    malkounAmplitude k4e2k3Graph (n7Path 0) = 20736 := by
  have hmatch : ∀ u v, k4e2k3Graph.Adj u v → ∀ k,
      planarUnnormSpinor (n7Point 0 u) (n7Point 0 v) k =
        ((scaleFromInts (((n7PtsX v - n7PtsX u).natAbs : ℤ))
          (n7PtsX v - n7PtsX u) 0 : ℤ) : ℂ) * GI.toC (spinorsN7ColGI u v k) := by
    intro u v huv
    rcases spinorsN7ColGI_ok u v huv with ⟨_, hr_nn, hr_sq, h0re, h0im, h1re, h1im⟩
    exact match_collinear_n7 u v (n7PtsX v - n7PtsX u) (((n7PtsX v - n7PtsX u).natAbs : ℤ))
      _ (spinorsN7ColGI u v) hr_nn
      (by simp [n7Point, Int.cast_sub]) (by simp [n7Point]) hr_sq h0re h0im h1re h1im
  have hscale : ∀ u v, k4e2k3Graph.Adj u v →
      scaleFromInts (((n7PtsX v - n7PtsX u).natAbs : ℤ)) (n7PtsX v - n7PtsX u) 0 ≠ 0 :=
    fun u v huv => (spinorsN7ColGI_ok u v huv).1
  rw [malkounAmplitude_eq_planarUnnorm k4e2k3Graph (n7Path 0) (n7Path_planar 0)]
  change malkounAmplitudeOfSpinors k4e2k3Graph
      (fun u v => planarUnnormSpinor (n7Point 0 u) (n7Point 0 v)) = 20736
  rw [malkounAmplitudeOfSpinors_congr k4e2k3Graph _
      (fun u v k => ((scaleFromInts (((n7PtsX v - n7PtsX u).natAbs : ℤ))
        (n7PtsX v - n7PtsX u) 0 : ℤ) : ℂ) * GI.toC (spinorsN7ColGI u v k)) hmatch]
  rw [malkounAmplitude_scale_invariant k4e2k3Graph _
      (fun u v huv => Int.cast_ne_zero.mpr (hscale u v huv))
      (fun u v k => GI.toC (spinorsN7ColGI u v k))]
  simp only [malkounAmplitudeOfSpinors, ← malkounNum_k4e2k3_giToC, ← malkounDen_k4e2k3_giToC,
    cert_n7_col_num, cert_n7_col_den, GI.toC_ofInt]
  norm_num

private lemma nonneg_sq_le_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ≤ b ↔ a * a ≤ b * b := by
  constructor
  · intro hab; exact mul_self_le_mul_self ha hab
  · intro hsq
    by_contra! hlt
    have hdiff : 0 < a - b := sub_pos.mpr hlt
    have hsum : 0 < a + b := add_pos_of_pos_of_nonneg (lt_of_le_of_lt hb hlt) hb
    have hpos : 0 < (a - b) * (a + b) := mul_pos hdiff hsum
    linarith

private noncomputable def n7ScaledSpinors (u v : Fin 7) (k : Fin 2) : ℂ :=
  ((n7Scale : ℤ) : ℂ) * planarUnnormSpinor (n7Point 1 u) (n7Point 1 v) k

private lemma spinorsN7Iv_mem : ∀ u v : Fin 7, k4e2k3Graph.Adj u v →
    ∀ k : Fin 2, (spinorsN7Iv u v k).Mem (n7ScaledSpinors u v k) := by
  intro u v huv k
  rcases distN7Lo_ok u v huv with ⟨hlo_nn, hlo_sq, hhi_sq⟩
  let dx := n7PtsX v - n7PtsX u
  let dy := n7PtsY v - n7PtsY u
  let r_real := euclidNorm (fun j => n7Point 1 v j - n7Point 1 u j)
  have hS_pos : (0 : ℝ) < (n7Scale : ℝ) := by norm_num [n7Scale]
  have hr_nn : 0 ≤ r_real := Real.sqrt_nonneg _
  have hr_sq : ((n7Scale : ℝ) * r_real) * ((n7Scale : ℝ) * r_real) =
      ((n7Scale * n7Scale * (dx * dx + dy * dy) : ℤ) : ℝ) := by
    have hnorm_sq : r_real * r_real = (dx : ℝ) * (dx : ℝ) + (dy : ℝ) * (dy : ℝ) := by
      simp only [r_real, euclidNorm, ← sq]
      rw [Real.sq_sqrt (by positivity)]
      simp only [n7Point, mul_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero, dx, dy]
      push_cast
      ring
    calc ((n7Scale : ℝ) * r_real) * ((n7Scale : ℝ) * r_real)
        = (n7Scale : ℝ) * (n7Scale : ℝ) * (r_real * r_real) := by ring
      _ = ((n7Scale * n7Scale * (dx * dx + dy * dy) : ℤ) : ℝ) := by
            rw [hnorm_sq]; push_cast; ring
  have hlo_R : (distN7Lo u v : ℝ) ≤ (n7Scale : ℝ) * r_real := by
    have hlo_R_nn : (0 : ℝ) ≤ (distN7Lo u v : ℝ) := by exact_mod_cast hlo_nn
    refine (nonneg_sq_le_iff hlo_R_nn (mul_nonneg hS_pos.le hr_nn)).mpr ?_
    rw [hr_sq]
    exact_mod_cast hlo_sq
  have hhi_R : (n7Scale : ℝ) * r_real ≤ ((distN7Lo u v + 1 : ℤ) : ℝ) := by
    have hhi_R_nn : (0 : ℝ) ≤ ((distN7Lo u v + 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 ≤ distN7Lo u v + 1)
    refine (nonneg_sq_le_iff (mul_nonneg hS_pos.le hr_nn) hhi_R_nn).mpr ?_
    rw [hr_sq]
    exact_mod_cast hhi_sq
  rcases fin2_cases k with rfl | rfl
  · simp only [n7ScaledSpinors, planarUnnormSpinor, spinorsN7Iv, CIntIv.Mem, IntIv.Mem,
      IntIv.zero]
    have hre : (((n7Scale : ℤ) : ℂ) * (r_real : ℂ)).re = (n7Scale : ℝ) * r_real := by
      change ((n7Scale : ℝ) * (r_real : ℂ)).re = _; simp
    have him : (((n7Scale : ℤ) : ℂ) * (r_real : ℂ)).im = 0 := by
      change ((n7Scale : ℝ) * (r_real : ℂ)).im = _; simp
    rw [hre, him]
    exact ⟨⟨hlo_R, by exact_mod_cast hhi_R⟩, ⟨le_rfl, le_rfl⟩⟩
  · simp only [n7ScaledSpinors, planarUnnormSpinor, spinorsN7Iv, CIntIv.Mem]
    have hdx_r : n7Point 1 v 0 - n7Point 1 u 0 = (dx : ℝ) := by simp [n7Point, dx]
    have hdy_r : n7Point 1 v 1 - n7Point 1 u 1 = (dy : ℝ) := by simp [n7Point, dy]
    rw [hdx_r, hdy_r]
    have hre : (((n7Scale : ℤ) : ℂ) * (((dx : ℝ) : ℂ) + Complex.I * ((dy : ℝ) : ℂ))).re =
        ((n7Scale * dx : ℤ) : ℝ) := by
      push_cast; simp
    have him : (((n7Scale : ℤ) : ℂ) * (((dx : ℝ) : ℂ) + Complex.I * ((dy : ℝ) : ℂ))).im =
        ((n7Scale * dy : ℤ) : ℝ) := by
      push_cast; simp
    change (IntIv.ofInt (n7Scale * dx)).Mem
        (((n7Scale : ℤ) : ℂ) * (((dx : ℝ) : ℂ) + Complex.I * ((dy : ℝ) : ℂ))).re ∧
      (IntIv.ofInt (n7Scale * dy)).Mem
        (((n7Scale : ℤ) : ℂ) * (((dx : ℝ) : ℂ) + Complex.I * ((dy : ℝ) : ℂ))).im
    rw [hre, him]
    exact ⟨IntIv.ofInt_mem _, IntIv.ofInt_mem _⟩

private lemma div_re_neg_of_iv_dot_neg {N D : ℂ} {numIv denIv : CIntIv}
    (hD : D ≠ 0) (hN_mem : numIv.Mem N) (hD_mem : denIv.Mem D)
    (hdot : ((numIv.re.mul denIv.re).add (numIv.im.mul denIv.im)).hi < 0) :
    (N / D).re < 0 := by
  have hdot_mem : ((numIv.re.mul denIv.re).add (numIv.im.mul denIv.im)).Mem
      (N.re * D.re + N.im * D.im) :=
    IntIv.add_mem (IntIv.mul_mem hN_mem.1 hD_mem.1) (IntIv.mul_mem hN_mem.2 hD_mem.2)
  have hhi : ((((numIv.re.mul denIv.re).add (numIv.im.mul denIv.im)).hi : ℤ) : ℝ) < 0 :=
    Int.cast_lt.mpr hdot
  have hneg : N.re * D.re + N.im * D.im < 0 := lt_of_le_of_lt hdot_mem.2 hhi
  have hre : (N / D).re = (N.re * D.re + N.im * D.im) / Complex.normSq D := by
    rw [Complex.div_re]
    ring
  rw [hre]
  exact div_neg_of_neg_of_pos hneg (Complex.normSq_pos.mpr hD)

@[irreducible] private noncomputable def n7NumC : ℂ :=
  malkounNum k4e2k3Graph n7ScaledSpinors

@[irreducible] private noncomputable def n7DenC : ℂ :=
  malkounDen k4e2k3Graph n7ScaledSpinors

/-- Value of $\mathcal{A}_{H_7}(\gamma(1))$ shielded as `@[irreducible]` so `LT.lt` on `ℝ`
does not unfold `malkounNum` during elaboration. -/
@[irreducible] noncomputable def n7AmpOne : ℂ :=
  malkounAmplitude k4e2k3Graph (n7Path 1)

lemma n7AmpOne_eq : n7AmpOne = malkounAmplitude k4e2k3Graph (n7Path 1) := by
  unfold n7AmpOne; rfl

private lemma n7NumC_eq : n7NumC = malkounNum k4e2k3Graph n7ScaledSpinors := by
  unfold n7NumC; rfl

private lemma n7DenC_eq : n7DenC = malkounDen k4e2k3Graph n7ScaledSpinors := by
  unfold n7DenC; rfl

theorem n7AmpOne_re_neg : n7AmpOne.re < 0 := by
  have hS_ne : ((n7Scale : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by decide)
  have hamp : n7AmpOne = n7NumC / n7DenC := by
    rw [n7AmpOne_eq, n7NumC_eq, n7DenC_eq]
    rw [malkounAmplitude_eq_planarUnnorm k4e2k3Graph (n7Path 1) (n7Path_planar 1)]
    have hsc := malkounAmplitude_scale_invariant k4e2k3Graph
      (fun _ _ => ((n7Scale : ℤ) : ℂ)) (fun _ _ _ => hS_ne)
      (fun u v => planarUnnormSpinor (n7Point 1 u) (n7Point 1 v))
    exact hsc.symm
  have hden_ne : n7DenC ≠ 0 := by
    rw [n7DenC_eq]
    have hden0 := malkounDen_planarUnnorm_ne_zero k4e2k3Graph (n7Path 1) (n7Path_planar 1)
    have hfactor : malkounDen k4e2k3Graph n7ScaledSpinors =
        ∏ _e : OriEdge k4e2k3Graph, ((n7Scale : ℤ) : ℂ) * ((n7Scale : ℤ) : ℂ) *
          omega (planarUnnormSpinor (n7Point 1 _e.1.1) (n7Point 1 _e.1.2))
                (planarUnnormSpinor (n7Point 1 _e.1.2) (n7Point 1 _e.1.1)) := by
      refine Finset.prod_congr rfl fun e _ => ?_
      change omega (fun k => ((n7Scale : ℤ) : ℂ) * planarUnnormSpinor (n7Point 1 e.1.1) (n7Point 1 e.1.2) k)
                   (fun k => ((n7Scale : ℤ) : ℂ) * planarUnnormSpinor (n7Point 1 e.1.2) (n7Point 1 e.1.1) k) = _
      rw [omega_smul]
    rw [hfactor, Finset.prod_mul_distrib]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ => mul_ne_zero hS_ne hS_ne) hden0
  have hN : n7NumVal.Mem n7NumC := by
    rw [n7NumC_eq, ← cert_n7_num_val]
    exact k4e2k3NumIv_mem spinorsN7Iv n7ScaledSpinors spinorsN7Iv_mem
  have hD : n7DenVal.Mem n7DenC := by
    rw [n7DenC_eq, ← cert_n7_den_val]
    exact k4e2k3DenIv_mem spinorsN7Iv n7ScaledSpinors spinorsN7Iv_mem
  rw [hamp]
  exact div_re_neg_of_iv_dot_neg hden_ne hN hD cert_n7_dot_neg

private lemma continuous_planarUnnorm_n7Path (u v : Fin 7) (k : Fin 2) :
    Continuous (fun t : ℝ => planarUnnormSpinor (n7Point t u) (n7Point t v) k) := by
  fin_cases k
  · dsimp [planarUnnormSpinor, euclidNorm, n7Point]
    fun_prop
  · dsimp [planarUnnormSpinor, n7Point]
    fun_prop

theorem continuous_malkounAmplitude_n7Path :
    Continuous (fun t : ℝ => malkounAmplitude k4e2k3Graph (n7Path t)) := by
  have hfun : (fun t : ℝ => malkounAmplitude k4e2k3Graph (n7Path t)) =
      fun t : ℝ =>
        malkounNum k4e2k3Graph (fun u v => planarUnnormSpinor (n7Point t u) (n7Point t v)) /
        malkounDen k4e2k3Graph (fun u v => planarUnnormSpinor (n7Point t u) (n7Point t v)) := by
    ext t
    exact malkounAmplitude_eq_planarUnnorm k4e2k3Graph (n7Path t) (n7Path_planar t)
  rw [hfun]
  have hspin : ∀ u v k,
      Continuous (fun t : ℝ => planarUnnormSpinor (n7Point t u) (n7Point t v) k) :=
    continuous_planarUnnorm_n7Path
  have homega : ∀ (f g : Fin 2 → ℝ → ℂ), (∀ k, Continuous (f k)) → (∀ k, Continuous (g k)) →
      Continuous (fun t => omega (fun k => f k t) (fun k => g k t)) := by
    intro f g hf hg
    dsimp [omega]
    fun_prop
  have hnum : Continuous (fun t : ℝ =>
      malkounNum k4e2k3Graph (fun u v => planarUnnormSpinor (n7Point t u) (n7Point t v))) := by
    dsimp [malkounNum]
    fun_prop (disch := exact fun _ _ _ => _)
  have hden : Continuous (fun t : ℝ =>
      malkounDen k4e2k3Graph (fun u v => planarUnnormSpinor (n7Point t u) (n7Point t v))) := by
    dsimp [malkounDen]
    fun_prop
  exact hnum.div hden fun t =>
    malkounDen_planarUnnorm_ne_zero k4e2k3Graph (n7Path t) (n7Path_planar t)

private lemma exists_n7Path_zero :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) 1, malkounAmplitude k4e2k3Graph (n7Path t₀) = 0 := by
  let f : ℝ → ℝ := fun t => (malkounAmplitude k4e2k3Graph (n7Path t)).re
  have hf_cont : Continuous f := Complex.continuous_re.comp continuous_malkounAmplitude_n7Path
  have h0 : f 0 = 20736 := by
    dsimp only [f]
    rw [malkounAmplitude_n7Path_zero]
    norm_num
  have h1_eq : f 1 = n7AmpOne.re := by
    dsimp only [f]
    rw [← n7AmpOne_eq]
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
    refine ⟨?_, by rw [h0]; norm_num⟩
    rw [h1_eq]
    exact n7AmpOne_re_neg.le
  rcases intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf_cont.continuousOn hmem with
    ⟨t₀, ht₀_icc, ht₀_re⟩
  refine ⟨t₀, ht₀_icc, ?_⟩
  have ht₀_im : (malkounAmplitude k4e2k3Graph (n7Path t₀)).im = 0 :=
    planar_amplitude_im_eq_zero k4e2k3Graph (n7Path t₀) (n7Path_planar t₀)
  exact Complex.ext (by simpa [f] using ht₀_re) ht₀_im

/-- **Formal Disproof of Malkoun's Conjecture A on a 7-vertex 2-vertex-connected planar graph**
(`k4e2k3Graph`, $n=7, m=11, \kappa=2$). -/
theorem disproof_malkoun_n7_biconnected_conjecture_A :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ IsTwoVertexConnected G ∧ ∃ x : ConfigSpace G, malkounAmplitude G x = 0 := by
  rcases exists_n7Path_zero with ⟨t₀, _, ht₀⟩
  exact ⟨7, k4e2k3Graph, instDecidableRelK4e2k3, k4e2k3Graph_connected,
    k4e2k3Graph_twoVertexConnected, n7Path t₀, ht₀⟩

/-- **Formal Disproof of Malkoun's Conjecture B on a 7-vertex 2-vertex-connected planar graph**
(`k4e2k3Graph`, $n=7, m=11, \kappa=2$). -/
theorem disproof_malkoun_n7_biconnected_conjecture_B :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ IsTwoVertexConnected G ∧ ∃ x : ConfigSpace G, ‖malkounAmplitude G x‖ < 1 := by
  rcases exists_n7Path_zero with ⟨t₀, _, ht₀⟩
  exact ⟨7, k4e2k3Graph, instDecidableRelK4e2k3, k4e2k3Graph_connected,
    k4e2k3Graph_twoVertexConnected, n7Path t₀, by rw [ht₀, norm_zero]; norm_num⟩

/-- **Formal Disproof of Malkoun's Section 6 Real-Negativity Question on a 7-vertex
2-vertex-connected planar graph** (`k4e2k3Graph`, $n=7, m=11, \kappa=2$ at `n7Path 1`). -/
theorem disproof_malkoun_n7_biconnected_section_6 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ IsTwoVertexConnected G ∧ ∃ x : ConfigSpace G,
        (malkounAmplitude G x).re < 0 ∧ (malkounAmplitude G x).im = 0 := by
  refine ⟨7, k4e2k3Graph, instDecidableRelK4e2k3, k4e2k3Graph_connected,
    k4e2k3Graph_twoVertexConnected, n7Path 1, ?_,
    planar_amplitude_im_eq_zero k4e2k3Graph (n7Path 1) (n7Path_planar 1)⟩
  rw [← n7AmpOne_eq]
  exact n7AmpOne_re_neg

end HomotopyDisproof

end Matematyka.MalkounN7Counterexample
