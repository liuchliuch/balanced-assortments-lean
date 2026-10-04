import BalancedAssortments.FixedSupportCostLists
import BalancedAssortments.FixedSupportAlgorithm

namespace BalancedAssortments.FixedSupportCostPoints
open ComplexityTimeFractions (decode Valid width zero one zero_valid one_valid zero_decode one_decode)
open FixedSupportCostRational FixedSupportCostLists

abbrev Product := Fraction × Fraction

def Product.Valid (p : Product) : Prop := ComplexityTimeFractions.Valid p.1 ∧ ComplexityTimeFractions.Valid p.2
def Product.Width (p : Product) (B : ℕ) : Prop := width p.1 ≤ B ∧ width p.2 ≤ B

def two : Fraction := ⟨([false, true], []), [true]⟩
@[simp] theorem two_valid : Valid two := by norm_num [two, Valid, ComplexityTimeBinary.value]
@[simp] theorem two_decode : decode two = 2 := by norm_num [two, decode, ComplexityTimeVerifier.zvalue, ComplexityTimeBinary.value]
@[simp] theorem two_width : width two = 2 := rfl

def within (upper x : Fraction) : Bool × ℕ :=
  let a := FixedSupportCostRational.le zero x
  let b := FixedSupportCostRational.le x upper
  (a.1 && b.1, a.2+b.2+2)

theorem within_correct (upper x : Fraction) (hu : Valid upper) (hx : Valid x) :
    (within upper x).1 = true ↔ 0 ≤ decode x ∧ decode x ≤ decode upper := by
  simp only [within, Bool.and_eq_true, le_correct zero x zero_valid hx, le_correct x upper hx hu, zero_decode]

theorem within_cost (upper x : Fraction) {B : ℕ}
    (hu : width upper ≤ B) (hx : width x ≤ B) :
    (within upper x).2 ≤ 32768*(B+1)^2 := by
  have ha := le_cost (x := zero) (by simp : width zero ≤ 1) hx
  have hb := le_cost hx hu
  simp only [within]
  nlinarith

def midpoint (x y : Fraction) : Fraction × ℕ :=
  let a := addFresh x y
  let d := divideFresh a.1 two
  (d.1, a.2+d.2+4)

theorem midpoint_valid (x y : Fraction) (hx : Valid x) (hy : Valid y) : Valid (midpoint x y).1 :=
  divideFresh_valid _ _ (addFresh_valid x y hx hy) two_valid

theorem midpoint_decode (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    decode (midpoint x y).1 = (decode x+decode y)/2 := by
  simp only [midpoint, divideFresh_decode, addFresh_decode x y hx hy, two_decode]

theorem midpoint_width (x y : Fraction) {B : ℕ} (hx : width x ≤ B) (hy : width y ≤ B) :
    width (midpoint x y).1 ≤ 3*B+7 := by
  have ha := addFresh_width hx hy
  have hd := divideFresh_width_valid ha (by simp : width two ≤ 2) two_valid
  dsimp only [midpoint]
  omega

theorem midpoint_cost (x y : Fraction) {B : ℕ} (hx : width x ≤ B) (hy : width y ≤ B) :
    (midpoint x y).2 ≤ 65536*(B+1)^2 := by
  have ha := addFresh_cost hx hy
  have haw := addFresh_width hx hy
  have hd := divideFresh_cost haw (by simp : width two ≤ 2)
  simp only [midpoint]
  nlinarith

/-- Pairwise score crossing. A zero slope returns zero, an already-included
endpoint, so no semantic root is invented when scores are parallel. -/
def crossing (p q : Product) : Fraction × ℕ :=
  let a := multiplyFresh p.1 p.2
  let b := multiplyFresh q.1 q.2
  let top := subtractFresh a.1 b.1
  let bot := subtractFresh p.2 q.2
  let root := divideFresh top.1 bot.1
  (root.1, a.2+b.2+top.2+bot.2+root.2+8)

def crossingValue (p q : ℚ × ℚ) : ℚ := (p.1*p.2-q.1*q.2)/(p.2-q.2)

theorem crossing_valid (p q : Product) (hp : p.Valid) (hq : q.Valid) : Valid (crossing p q).1 := by
  apply divideFresh_valid
  · exact subtractFresh_valid _ _ (multiplyFresh_valid _ _ hp.1 hp.2) (multiplyFresh_valid _ _ hq.1 hq.2)
  · exact subtractFresh_valid _ _ hp.2 hq.2

theorem crossing_decode (p q : Product) (hp : p.Valid) (hq : q.Valid) :
    decode (crossing p q).1 = crossingValue (decode p.1, decode p.2) (decode q.1, decode q.2) := by
  simp only [crossing, crossingValue, divideFresh_decode,
    subtractFresh_decode _ _ (multiplyFresh_valid _ _ hp.1 hp.2) (multiplyFresh_valid _ _ hq.1 hq.2),
    subtractFresh_decode _ _ hp.2 hq.2, multiplyFresh_decode]

theorem crossing_width (p q : Product) {B : ℕ} (hp : p.Width B) (hq : q.Width B)
    (hvp : p.Valid) (hvq : q.Valid) : width (crossing p q).1 ≤ 16*(B+1) := by
  have ha := multiplyFresh_width hp.1 hp.2
  have hb := multiplyFresh_width hq.1 hq.2
  have ht := subtractFresh_width ha hb
  have hd := subtractFresh_width hp.2 hq.2
  have hr := divideFresh_width_valid ht hd (subtractFresh_valid _ _ hvp.2 hvq.2)
  dsimp only [crossing]
  omega

theorem crossing_cost (p q : Product) {B : ℕ} (hp : p.Width B) (hq : q.Width B) :
    (crossing p q).2 ≤ 1048576*(B+1)^2 := by
  have ha := multiplyFresh_cost hp.1 hp.2
  have hb := multiplyFresh_cost hq.1 hq.2
  have haw := multiplyFresh_width hp.1 hp.2
  have hbw := multiplyFresh_width hq.1 hq.2
  have ht := subtractFresh_cost haw hbw
  have hd := subtractFresh_cost hp.2 hq.2
  have htw := subtractFresh_width haw hbw
  have hdw := subtractFresh_width hp.2 hq.2
  have hr := divideFresh_cost htw hdw
  dsimp only [crossing]
  nlinarith

/-- All critical score cuts; numerical duplicates are retained intentionally.
This remains polynomial and avoids requiring rational normalization or hashing. -/
def criticalPoints (ps : List Product) : List Fraction × ℕ :=
  let maximum := foldExtreme false zero (ps.map Prod.fst)
  let roots := FPTASCostLoops.cross (fun p q => (some (crossing p q).1, (crossing p q).2)) ps ps
  let filtered := filterCost (within maximum.1) (ps.map Prod.fst ++ roots.1)
  (zero :: maximum.1 :: filtered.1,
    maximum.2+roots.2+filtered.2+12*ps.length+8)

def scorePoints (ps : List Product) : List Fraction × ℕ :=
  let cuts := criticalPoints ps
  let mids := FPTASCostLoops.cross (fun x y => (some (midpoint x y).1, (midpoint x y).2)) cuts.1 cuts.1
  (cuts.1 ++ mids.1, cuts.2+mids.2+cuts.1.length+4)

private theorem all_cross {A B C : Type*} (f : A → B → C × ℕ) (xs : List A) (ys : List B) :
    (FPTASCostLoops.cross (fun x y => (some (f x y).1, (f x y).2)) xs ys).1 =
      xs.flatMap (fun x => ys.map (fun y => (f x y).1)) := by
  simp [FPTASCostLoops.cross_eq]

private theorem all_cross_length {A B C : Type*} (f : A → B → C × ℕ) (xs : List A) (ys : List B) :
    (FPTASCostLoops.cross (fun x y => (some (f x y).1, (f x y).2)) xs ys).1.length = xs.length*ys.length := by
  rw [all_cross]
  induction xs <;> simp [*, Nat.add_mul, Nat.add_comm]

private theorem all_cross_property {A B C : Type*} (f : A → B → C × ℕ) (xs : List A) (ys : List B)
    (P : C → Prop) (hf : ∀ x ∈ xs, ∀ y ∈ ys, P (f x y).1) :
    ∀ z ∈ (FPTASCostLoops.cross (fun x y => (some (f x y).1, (f x y).2)) xs ys).1, P z := by
  rw [all_cross]
  intro z hz
  obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  exact hf x hx y hy

theorem criticalPoints_length (ps : List Product) :
    (criticalPoints ps).1.length ≤ ps.length*ps.length+ps.length+2 := by
  have hh := List.length_filter_le (fun x => (within (foldExtreme false zero (ps.map Prod.fst)).1 x).1)
    (ps.map Prod.fst ++ (FPTASCostLoops.cross (fun p q => (some (crossing p q).1, (crossing p q).2)) ps ps).1)
  simp only [criticalPoints, List.length_cons, filterCost_value, List.length_append, List.length_map,
    all_cross_length]
  simp only [List.length_append, List.length_map, all_cross_length] at hh
  omega

theorem criticalPoints_valid (ps : List Product) (hv : ∀ p ∈ ps, p.Valid) :
    ∀ x ∈ (criticalPoints ps).1, Valid x := by
  have hp : ∀ x ∈ ps.map Prod.fst, Valid x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hv p hp).1
  have hm := foldExtreme_valid false zero (ps.map Prod.fst) zero_valid hp
  have hr := all_cross_property crossing ps ps Valid (fun p hp q hq => crossing_valid p q (hv p hp) (hv q hq))
  intro x hx
  simp only [criticalPoints, List.mem_cons, filterCost_value] at hx
  rcases hx with rfl | rfl | hx
  · exact zero_valid
  · exact hm
  · have hx' := List.mem_of_mem_filter hx
    rcases List.mem_append.mp hx' with hx' | hx'
    · exact hp x hx'
    · exact hr x hx'

theorem criticalPoints_width (ps : List Product) {B : ℕ} (hB : 1 ≤ B)
    (hv : ∀ p ∈ ps, p.Valid) (hw : ∀ p ∈ ps, p.Width B) :
    ∀ x ∈ (criticalPoints ps).1, width x ≤ 16*(B+1) := by
  have hp : ∀ x ∈ ps.map Prod.fst, width x ≤ B := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hw p hp).1
  have hz : width zero ≤ B := by simpa using hB
  have hm := (foldExtreme_width_cost false zero (ps.map Prod.fst) hz hp).1
  have hr := all_cross_property crossing ps ps (fun x => width x ≤ 16*(B+1))
    (fun p hp q hq => crossing_width p q (hw p hp) (hw q hq) (hv p hp) (hv q hq))
  intro x hx
  simp only [criticalPoints, List.mem_cons, filterCost_value] at hx
  rcases hx with rfl | rfl | hx
  · simp; omega
  · omega
  · have hx' := List.mem_of_mem_filter hx
    rcases List.mem_append.mp hx' with hx' | hx'
    · have := hp x hx'; omega
    · exact hr x hx'

def criticalCostBudget (n B : ℕ) : ℕ :=
  (n*(2048*(2*B+1)^2+6)+1) +
  (n*(n*(1048576*(B+1)^2+5)+5)+1) +
  ((n+n*n)*(32768*(16*(B+1)+1)^2+5)+1) + 12*n+8

theorem criticalPoints_cost (ps : List Product) {B : ℕ} (hB : 1 ≤ B)
    (hv : ∀ p ∈ ps, p.Valid) (hw : ∀ p ∈ ps, p.Width B) :
    (criticalPoints ps).2 ≤ criticalCostBudget ps.length B := by
  have hp : ∀ x ∈ ps.map Prod.fst, width x ≤ B := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hw p hp).1
  have hz : width zero ≤ B := by simpa using hB
  have hm := foldExtreme_width_cost false zero (ps.map Prod.fst) hz hp
  have hr := FPTASCostLoops.cross_cost
    (fun p q => (some (crossing p q).1, (crossing p q).2)) ps ps
    (fun p hp q hq => crossing_cost p q (hw p hp) (hw q hq))
  have hrw := all_cross_property crossing ps ps (fun x => width x ≤ 16*(B+1))
    (fun p hp q hq => crossing_width p q (hw p hp) (hw q hq) (hv p hp) (hv q hq))
  have hf := filterCost_cost (within (foldExtreme false zero (ps.map Prod.fst)).1)
    (ps.map Prod.fst ++ (FPTASCostLoops.cross (fun p q => (some (crossing p q).1, (crossing p q).2)) ps ps).1)
    (C := 32768*(16*(B+1)+1)^2) (by
      intro x hx
      apply within_cost _ _ (hm.1.trans (by omega))
      rcases List.mem_append.mp hx with hx | hx
      · exact (hp x hx).trans (by omega)
      · exact hrw x hx)
  simp only [List.length_map] at hm
  simp only [List.length_append, List.length_map, all_cross_length] at hf
  dsimp only [criticalPoints, criticalCostBudget]
  omega

def pointCount (n : ℕ) : ℕ := n*n+n+2

theorem scorePoints_length (ps : List Product) :
    (scorePoints ps).1.length ≤ pointCount ps.length + (pointCount ps.length)^2 := by
  have hc := criticalPoints_length ps
  simp only [scorePoints, List.length_append, all_cross_length]
  dsimp [pointCount]
  nlinarith

theorem scorePoints_valid (ps : List Product) (hv : ∀ p ∈ ps, p.Valid) :
    ∀ x ∈ (scorePoints ps).1, Valid x := by
  have hc := criticalPoints_valid ps hv
  have hm := all_cross_property midpoint (criticalPoints ps).1 (criticalPoints ps).1 Valid
    (fun x hx y hy => midpoint_valid x y (hc x hx) (hc y hy))
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hc x hx
  · exact hm x hx

theorem scorePoints_width (ps : List Product) {B : ℕ} (hB : 1 ≤ B)
    (hv : ∀ p ∈ ps, p.Valid) (hw : ∀ p ∈ ps, p.Width B) :
    ∀ x ∈ (scorePoints ps).1, width x ≤ 64*(B+1) := by
  have hc := criticalPoints_width ps hB hv hw
  have hm := all_cross_property midpoint (criticalPoints ps).1 (criticalPoints ps).1
    (fun x => width x ≤ 64*(B+1)) (by
      intro x hx y hy
      have hh := midpoint_width x y (hc x hx) (hc y hy)
      omega)
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (hc x hx).trans (by omega)
  · exact hm x hx

/-- Explicit degree-four-in-n score-arrangement bit/list budget. -/
def scoreCostBudget (n B : ℕ) : ℕ :=
  criticalCostBudget n B +
    (pointCount n)*((pointCount n)*(65536*(16*(B+1)+1)^2+5)+5)+1 + pointCount n + 4

theorem scorePoints_cost (ps : List Product) {B : ℕ} (hB : 1 ≤ B)
    (hv : ∀ p ∈ ps, p.Valid) (hw : ∀ p ∈ ps, p.Width B) :
    (scorePoints ps).2 ≤ scoreCostBudget ps.length B := by
  have hc := criticalPoints_width ps hB hv hw
  have hl := criticalPoints_length ps
  have hcc := criticalPoints_cost ps hB hv hw
  have hm := FPTASCostLoops.cross_cost
    (fun x y => (some (midpoint x y).1, (midpoint x y).2)) (criticalPoints ps).1 (criticalPoints ps).1
    (fun x hx y hy => midpoint_cost x y (hc x hx) (hc y hy))
  have hl' : (criticalPoints ps).1.length ≤ pointCount ps.length := hl
  have hmb : (FPTASCostLoops.cross (fun x y => (some (midpoint x y).1, (midpoint x y).2))
      (criticalPoints ps).1 (criticalPoints ps).1).2 ≤
      (pointCount ps.length)*((pointCount ps.length)*(65536*(16*(B+1)+1)^2+5)+5)+1 := by
    apply hm.trans
    gcongr
  dsimp only [scorePoints, scoreCostBudget]
  omega

end BalancedAssortments.FixedSupportCostPoints
