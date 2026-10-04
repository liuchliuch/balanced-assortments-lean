import BalancedAssortments.CookLevinRawCostShape

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

def moveCost (b : ℕ) : ℕ := 64*(b+1)
lemma rawMoveMatch_cost {b : ℕ} (m : Move) {old next : List Bool}
    (ho : old.length≤b) (hn : next.length≤b) : (rawMoveMatch m old next).2≤ moveCost b := by
  cases m <;> simp only [rawMoveMatch,addCarry_cost,addCarry_length,List.length_nil,Nat.max_zero,compareBits_cost,moveCost] <;> omega

def targetProfile (N b : ℕ) : CostProfile :=
  ⟨1,N*(moveCost b+labelCost b+9)+6*N+6⟩
lemma rawHeadTarget_bound {N b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {next old : List Bool} (hn : next.length≤b) (ho : old.length≤b)
    (m : Move) (cells : List (List Bool)) (nc : cells.length≤N) (hc : ListWidths b cells) :
    CodeBound (targetProfile N b).len (targetProfile N b).cost (rawHeadTarget d next old m cells) := by
  let f := fun cell =>
    let test := rawMoveMatch m old cell
    let label := headLabel d next cell
    (if test.1 then [label.1] else [],test.2+label.2+4)
  have hf : ∀ cell∈cells,(f cell).2≤ moveCost b+labelCost b+4 := by
    intro cell hcell
    have hm := rawMoveMatch_cost m ho (hc cell hcell)
    have hl := (headLabel_bounds hd hn (hc cell hcell)).2
    dsimp [f]
    omega
  have hfl : ∀ cell∈cells,(f cell).1.length≤1 := by
    intro cell hcell
    dsimp [f]; split <;> simp
  have hm := rawFlatMap_cost f cells (moveCost b+labelCost b+4) 1 hf hfl
  have hl : (rawFlatMap f cells).1.length≤cells.length := by
    rw [rawFlatMap_eq]
    simpa only [Nat.mul_one] using length_flatMap_le cells _ 1 hfl
  have hp := rawMap_cost (fun x : List Bool => (Encoding.bitPositive x,2)) (rawFlatMap f cells).1 2 (by simp)
  constructor
  · rfl
  · change (rawFlatMap f cells).2+(rawMap (fun x => (Encoding.bitPositive x,2)) (rawFlatMap f cells).1).2+4≤_
    change _≤N*(moveCost b+labelCost b+9)+6*N+6
    have he : moveCost b+labelCost b+4+1+4=moveCost b+labelCost b+9 := by omega
    rw [he] at hm
    have hh := Nat.mul_le_mul_right (moveCost b+labelCost b+9) nc
    omega

structure RuleWidths (b : ℕ) (r : RawRule) : Prop where
  source : r.source.length≤b
  target : r.target.length≤b
  read : r.read.length≤b
  write : r.write.length≤b

def changedProfile (N b : ℕ) : CostProfile :=
  ((forceProfile b).append ((forceProfile b).append (targetProfile N b))).guarded b
def unchangedProfile (N b : ℕ) : CostProfile := (CostProfile.loop N (copyProfile b)).guarded b
def ruleProfile (N b : ℕ) : CostProfile :=
  (forceProfile b).append ((forceProfile b).append
    ((CostProfile.loop N (changedProfile N b)).append (CostProfile.loop N (unchangedProfile N b))))

lemma rawRuleBody_bound {N b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {old next : List Bool} (ho : old.length≤b) (hn : next.length≤b)
    (cells symbols : List (List Bool)) (nc : cells.length≤N) (na : symbols.length≤N)
    (hc : ListWidths b cells) (ha : ListWidths b symbols) (r : RawRule) (hr : RuleWidths b r) :
    CodeBound (ruleProfile N b).len (ruleProfile N b).cost (rawRuleBody d old next cells symbols r) := by
  apply bound_append (bound_force (stateLabel_bounds hd ho hr.source).2)
  apply bound_append (bound_force (stateLabel_bounds hd hn hr.target).2)
  apply bound_append
  · apply bound_flatMap cells _ nc
    intro p hp
    apply bound_guard true (headLabel_bounds hd ho (hc p hp)).2
    apply bound_append (bound_force (tapeLabel_bounds hd ho (hc p hp) hr.read).2)
    exact bound_append (bound_force (tapeLabel_bounds hd hn (hc p hp) hr.write).2)
      (rawHeadTarget_bound hd hn (hc p hp) r.move cells nc hc)
  · apply bound_flatMap cells _ nc
    intro p hp
    apply bound_guard false (headLabel_bounds hd ho (hc p hp)).2
    apply bound_flatMap symbols _ na
    intro a haa
    exact bound_copy (tapeLabel_bounds hd ho (hc p hp) (ha a haa)).2
      (tapeLabel_bounds hd hn (hc p hp) (ha a haa)).2

def initialProfile (N b : ℕ) : CostProfile :=
  (forceProfile b).append ((forceProfile b).append (CostProfile.loop N (forceProfile b)))
lemma rawInitial_bound {N b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {start : List Bool} (hstart : start.length≤b)
    (cells symbols : List (List Bool)) (nc : cells.length≤N)
    (hc : ListWidths b cells) (hs : ListWidths b symbols) :
    CodeBound (initialProfile N b).len (initialProfile N b).cost (rawInitial d start cells symbols) := by
  apply bound_append (bound_force (stateLabel_bounds hd (Nat.zero_le _) hstart).2)
  apply bound_append (bound_force (headLabel_bounds hd (Nat.zero_le _) hd.t).2)
  apply bound_flatMap (cells.zip symbols) _ (by simpa only [List.length_zip] using (Nat.min_le_left cells.length symbols.length).trans nc)
  intro pair hp
  have hl := List.of_mem_zip hp
  exact bound_force (tapeLabel_bounds hd (Nat.zero_le _) (hc pair.1 hl.1) (hs pair.2 hl.2)).2

end BalancedAssortments.CookLevin
