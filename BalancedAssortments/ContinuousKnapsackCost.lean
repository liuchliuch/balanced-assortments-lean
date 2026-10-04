import BalancedAssortments.ContinuousKnapsack
import BalancedAssortments.FixedSupportCostRational

/-! Actual signed bit-fraction continuous-knapsack greedy execution. Cost
annotations count bit/list operations and are not arithmetic oracles. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace BalancedAssortments.ContinuousKnapsackCost
open ComplexityTimeFractions

structure Item where
  score : Fraction
  cap : Fraction
  deriving DecidableEq

def decodeItem (i : Item) : ContinuousKnapsack.Item := ⟨decode i.score, decode i.cap⟩
def ValidItem (i : Item) : Prop := Valid i.score ∧ Valid i.cap

def zeroAlloc : List Item → List Fraction × ℕ
  | [] => ([], 1)
  | _ :: items => let r := zeroAlloc items; (zero :: r.1, r.2+4)

@[simp] theorem zeroAlloc_length (items : List Item) : (zeroAlloc items).1.length = items.length := by
  induction items <;> simp [zeroAlloc, *]

@[simp] theorem zeroAlloc_decode (items : List Item) :
    (zeroAlloc items).1.map decode = List.replicate items.length 0 := by
  induction items <;> simp [zeroAlloc, *, List.replicate_succ]

@[simp] theorem zeroAlloc_cost (items : List Item) : (zeroAlloc items).2 = 4*items.length+1 := by
  induction items <;> simp [zeroAlloc, *] <;> omega

theorem zeroAlloc_valid (items : List Item) : ∀ x ∈ (zeroAlloc items).1, Valid x := by
  induction items with
  | nil => simp [zeroAlloc]
  | cons i items ih => simpa [zeroAlloc] using And.intro zero_valid ih

theorem zeroAlloc_width (items : List Item) : ∀ x ∈ (zeroAlloc items).1, width x ≤ 1 := by
  induction items with
  | nil => simp [zeroAlloc]
  | cons i items ih => simpa [zeroAlloc] using And.intro (show width zero ≤ 1 by simp) ih

/-- Exact raw bit-list implementation of greedy allocation. Subtraction is
fresh-oriented, so the growing residual budget is never repeatedly doubled. -/
def solve (B : Fraction) : List Item → List Fraction × ℕ
  | [] => ([], 1)
  | i :: items =>
      let positive := FixedSupportCostRational.le i.score zero
      if positive.1 then
        let zs := zeroAlloc (i::items)
        (zs.1, positive.2+zs.2+4)
      else
        let full := FixedSupportCostRational.le B i.cap
        if full.1 then
          let zs := zeroAlloc items
          (B::zs.1, positive.2+full.2+zs.2+6)
        else
          let remaining := FixedSupportCostRational.subtractFresh B i.cap
          let r := solve remaining.1 items
          (i.cap::r.1, positive.2+full.2+remaining.2+r.2+8)

@[simp] theorem solve_length (B : Fraction) (items : List Item) :
    (solve B items).1.length = items.length := by
  induction items generalizing B with
  | nil => rfl
  | cons i items ih => simp only [solve]; split_ifs <;> simp [ih]

theorem solve_valid (B : Fraction) (items : List Item) (hB : Valid B)
    (hi : ∀ i ∈ items, ValidItem i) : ∀ x ∈ (solve B items).1, Valid x := by
  induction items generalizing B with
  | nil => simp [solve]
  | cons i items ih =>
    have hitem := hi i (by simp)
    have htail : ∀ j ∈ items, ValidItem j := fun j hj => hi j (by simp [hj])
    simp only [solve]
    split_ifs
    · exact zeroAlloc_valid _
    · simpa using And.intro hB (zeroAlloc_valid items)
    · exact List.forall_mem_cons.mpr ⟨hitem.2,
        ih _ (FixedSupportCostRational.subtractFresh_valid B i.cap hB hitem.2) htail⟩

/-- Decoding raw output gives exactly the allocation of the certified rational
solver, not merely some feasible allocation. -/
theorem solve_decode (B : Fraction) (items : List Item) (hB : Valid B)
    (hi : ∀ i ∈ items, ValidItem i) :
    (solve B items).1.map decode =
      (ContinuousKnapsack.solve (decode B) (items.map decodeItem)).1 := by
  induction items generalizing B with
  | nil => rfl
  | cons i items ih =>
    have hitem := hi i (by simp)
    have htail : ∀ j ∈ items, ValidItem j := fun j hj => hi j (by simp [hj])
    have hp := FixedSupportCostRational.le_correct i.score zero hitem.1 zero_valid
    have hb := FixedSupportCostRational.le_correct B i.cap hB hitem.2
    simp only [zero_decode] at hp
    by_cases hs : (FixedSupportCostRational.le i.score zero).1 = true
    · have hnp : ¬0 < decode i.score := not_lt.mpr (hp.mp hs)
      simp [solve, hs, ContinuousKnapsack.solve, decodeItem, hnp]
    · have hsp : 0 < decode i.score := lt_of_not_ge (fun h => hs (hp.mpr h))
      by_cases hf : (FixedSupportCostRational.le B i.cap).1 = true
      · have hbc := hb.mp hf
        simp [solve, hs, hf, ContinuousKnapsack.solve, decodeItem, hsp, hbc]
      · have hbc : ¬decode B ≤ decode i.cap := fun h => hf (hb.mpr h)
        have hd := FixedSupportCostRational.subtractFresh_decode B i.cap hB hitem.2
        have hvalid := FixedSupportCostRational.subtractFresh_valid B i.cap hB hitem.2
        simp [solve, hs, hf, ContinuousKnapsack.solve, decodeItem, hsp, hbc,
          ih _ hvalid htail, hd]

/-- The raw executable greedy solver satisfies the proved optimality theorem. -/
theorem solve_optimal (B : Fraction) (items : List Item) (hB : Valid B)
    (hi : ∀ i ∈ items, ValidItem i) (hBn : 0 ≤ decode B)
    (hc : ∀ i ∈ items, 0 ≤ decode i.cap)
    (hs : (items.map decodeItem).Pairwise (fun i j => j.score ≤ i.score)) :
    ContinuousKnapsack.Feasible (decode B) (items.map decodeItem) ((solve B items).1.map decode) ∧
      ∀ y, ContinuousKnapsack.Feasible (decode B) (items.map decodeItem) y →
        ContinuousKnapsack.profit (items.map decodeItem) y ≤
          ContinuousKnapsack.profit (items.map decodeItem) ((solve B items).1.map decode) := by
  rw [solve_decode B items hB hi]
  apply ContinuousKnapsack.solve_optimal _ _ hBn _ hs
  intro i him
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp him
  exact hc i hi


/-- Stored fraction widths grow only linearly in the number of filled items. -/
theorem solve_width (B : Fraction) (items : List Item) (a b : ℕ)
    (hB : width B ≤ a) (hi : ∀ i ∈ items, width i.score ≤ b ∧ width i.cap ≤ b) :
    ∀ x ∈ (solve B items).1, width x ≤ a + items.length*(2*b+2)+b+1 := by
  induction items generalizing B a with
  | nil => simp [solve]
  | cons i items ih =>
    have hitem := hi i (by simp)
    have htail : ∀ j ∈ items, width j.score ≤ b ∧ width j.cap ≤ b := fun j hj => hi j (by simp [hj])
    intro x hx
    simp only [solve] at hx
    split_ifs at hx
    · have hz := zeroAlloc_width (i::items) x hx
      omega
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_cons]; omega
      · have hz := zeroAlloc_width items x hx
        omega
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_cons]; omega
      · have hw := FixedSupportCostRational.subtractFresh_width hB hitem.2
        have hh := ih _ (a+2*b+2) hw htail x hx
        simp only [List.length_cons]
        nlinarith


/-- Polynomial charged bit/list running time. The residual budget width is
linear, so repeated fresh subtraction cannot hide exponential arithmetic. -/
theorem solve_cost (B : Fraction) (items : List Item) (a b : ℕ)
    (hB : width B ≤ a) (hi : ∀ i ∈ items, width i.score ≤ b ∧ width i.cap ≤ b) :
    (solve B items).2 ≤
      32768*(items.length+1)*(a+(items.length+1)*(2*b+2)+b+4)^2 := by
  induction items generalizing B a with
  | nil =>
    simp only [solve, List.length_nil]
    have hsq : 1 ≤ (a + (0+1)*(2*b+2)+b+4)^2 := by
      have hh : 1 ≤ a + (0+1)*(2*b+2)+b+4 := by omega
      exact Nat.one_le_pow _ _ hh
    nlinarith
  | cons i items ih =>
    have hitem := hi i (by simp)
    have htail : ∀ j ∈ items, width j.score ≤ b ∧ width j.cap ≤ b := fun j hj => hi j (by simp [hj])
    let X := a+(items.length+2)*(2*b+2)+b+4
    have hX : 4 ≤ X := by dsimp [X]; nlinarith
    have hN : items.length ≤ X := by dsimp [X]; nlinarith
    have hA : a+b+1 ≤ X := by dsimp [X]; nlinarith
    have hS : b+2 ≤ X := by dsimp [X]; nlinarith
    have hp0 := FixedSupportCostRational.le_cost hitem.1 (show width zero ≤ 1 by simp)
    have hp : (FixedSupportCostRational.le i.score zero).2 ≤ 2048*X^2 := by
      apply hp0.trans
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simpa using hS) 2)
    have hb0 := FixedSupportCostRational.le_cost hB hitem.2
    have hb : (FixedSupportCostRational.le B i.cap).2 ≤ 2048*X^2 :=
      hb0.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 2))
    have hs0 := FixedSupportCostRational.subtractFresh_cost hB hitem.2
    have hs : (FixedSupportCostRational.subtractFresh B i.cap).2 ≤ 4096*X^2+2 := by
      apply hs0.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 2)) 2
    change (solve B (i::items)).2 ≤ 32768*(items.length+2)*X^2
    simp only [solve]
    split_ifs
    · rw [zeroAlloc_cost]
      simp only [List.length_cons]
      have hstep : (FixedSupportCostRational.le i.score zero).2 + (4*(items.length+1)+1)+4 ≤ 32768*X^2 := by
        nlinarith only [hp, hX, hN]
      exact hstep.trans (Nat.mul_le_mul_right (X^2) (by omega))
    · rw [zeroAlloc_cost]
      have hstep : (FixedSupportCostRational.le i.score zero).2 +
          (FixedSupportCostRational.le B i.cap).2 + (4*items.length+1)+6 ≤ 32768*X^2 := by
        nlinarith only [hp, hb, hX, hN]
      exact hstep.trans (Nat.mul_le_mul_right (X^2) (by omega))
    · have hw := FixedSupportCostRational.subtractFresh_width hB hitem.2
      have hr := ih _ (a+2*b+2) hw htail
      have he : a+2*b+2+(items.length+1)*(2*b+2)+b+4 = X := by dsimp [X]; ring
      rw [he] at hr
      have hstep : (FixedSupportCostRational.le i.score zero).2 +
          (FixedSupportCostRational.le B i.cap).2 +
          (FixedSupportCostRational.subtractFresh B i.cap).2 + 8 ≤ 32768*X^2 := by
        nlinarith only [hp, hb, hs, hX]
      calc
        _ = ((FixedSupportCostRational.le i.score zero).2 +
              (FixedSupportCostRational.le B i.cap).2 +
              (FixedSupportCostRational.subtractFresh B i.cap).2 + 8) +
              (solve (FixedSupportCostRational.subtractFresh B i.cap).1 items).2 := by omega
        _ ≤ 32768*X^2 + 32768*(items.length+1)*X^2 := Nat.add_le_add hstep hr
        _ = _ := by ring

end BalancedAssortments.ContinuousKnapsackCost
