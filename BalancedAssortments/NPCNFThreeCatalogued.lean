import BalancedAssortments.NPCNFThree

namespace BalancedAssortments.NPCNF

def maxLabel : List ℕ → ℕ
  | [] => 0
  | x::xs => max x (maxLabel xs)

lemma label_le_max {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ maxLabel xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

def freshStart (input : Catalogued) : ℕ := maxLabel input.catalog+1

def reduceThree (input : Catalogued) : Catalogued := catalogue (toThree (freshStart input) input.formula).1

lemma freshStart_bounds {input : Catalogued} (h : input.Valid) :
    variablesBounded (freshStart input) input.formula := by
  intro c hc l hl
  exact Nat.lt_succ_of_le (label_le_max (h.2 c hc l hl))

theorem reduceThree_valid (input : Catalogued) : (reduceThree input).Valid := catalogue_valid _
theorem reduceThree_three (input : Catalogued) : ThreeCNF (reduceThree input).formula := toThree_three _ _

theorem reduceThree_sat_iff {input : Catalogued} (h : input.Valid) :
    (reduceThree input).Sat ↔ input.Sat := toThree_sat_iff (freshStart_bounds h)

end BalancedAssortments.NPCNF
