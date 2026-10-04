import BalancedAssortments.FixedSupportCostPoints
import BalancedAssortments.FixedSupportAlgorithmFinite

namespace BalancedAssortments.FixedSupportCostPoints
open ComplexityTimeFractions (decode Valid width zero zero_valid zero_decode)
open FixedSupportCostRational FixedSupportCostLists FixedSupportAlgorithm

def decodeProduct (p : Product) : ℚ × ℚ := (decode p.1, decode p.2)

def upperValue (ps : List (ℚ × ℚ)) : ℚ := (ps.map Prod.fst).foldl max 0

def criticalValues (ps : List (ℚ × ℚ)) : List ℚ :=
  [0, upperValue ps] ++ ((ps.map Prod.fst) ++ ps.flatMap (fun p => ps.map (crossingValue p))).filter
    (fun c => decide (0 ≤ c ∧ c ≤ upperValue ps))

def scoreValues (ps : List (ℚ × ℚ)) : List ℚ :=
  let C := criticalValues ps
  C ++ C.flatMap (fun a => C.map (fun b => (a+b)/2))

private theorem filter_within_decode (upper : Fraction) (xs : List Fraction)
    (hu : Valid upper) (hx : ∀ x ∈ xs, Valid x) :
    ((filterCost (within upper) xs).1.map decode) =
      (xs.map decode).filter (fun q => decide (0 ≤ q ∧ q ≤ decode upper)) := by
  rw [filterCost_value]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have he : (within upper x).1 = decide (0 ≤ decode x ∧ decode x ≤ decode upper) := by
      apply Bool.eq_iff_iff.mpr
      simpa using within_correct upper x hu (hx x (by simp))
    simp only [List.filter_cons, List.map_cons, he]
    split_ifs <;> simp [ih (fun y hy => hx y (by simp [hy]))]

theorem criticalPoints_decode (ps : List Product) (hv : ∀ p ∈ ps, p.Valid) :
    ((criticalPoints ps).1.map decode) = criticalValues (ps.map decodeProduct) := by
  have hp : ∀ x ∈ ps.map Prod.fst, Valid x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hv p hp).1
  have hm := foldExtreme_valid false zero (ps.map Prod.fst) zero_valid hp
  have hmd := foldExtreme_decode false zero (ps.map Prod.fst) zero_valid hp
  have hemax : decode (foldExtreme false zero (ps.map Prod.fst)).1 = upperValue (ps.map decodeProduct) := by
    simpa [extreme, upperValue, List.map_map, Function.comp_def, decodeProduct] using hmd
  let roots := (FPTASCostLoops.cross (fun p q => (some (crossing p q).1, (crossing p q).2)) ps ps).1
  have hr : ∀ x ∈ roots, Valid x := by
    intro x hx
    simp only [roots, FPTASCostLoops.cross_eq, List.filterMap_eq_map'] at hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact crossing_valid p q (hv p hp) (hv q hq)
  have hrd : roots.map decode = (ps.map decodeProduct).flatMap
      (fun p => (ps.map decodeProduct).map (crossingValue p)) := by
    simp only [roots, FPTASCostLoops.cross_eq, List.filterMap_eq_map',
      List.map_flatMap, List.map_map, List.flatMap_map, Function.comp_def]
    apply List.flatMap_congr
    intro p hp
    apply List.map_congr_left
    intro q hq
    exact crossing_decode p q (hv p hp) (hv q hq)
  have hf := filter_within_decode (foldExtreme false zero (ps.map Prod.fst)).1
    (ps.map Prod.fst ++ roots) hm (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hp x hx
      · exact hr x hx)
  simp only [criticalPoints, List.map_cons, zero_decode]
  change _ = criticalValues (ps.map decodeProduct)
  rw [hemax, hf, List.map_append, hrd, hemax]
  simp [criticalValues, List.map_map, Function.comp_def, decodeProduct]

theorem scorePoints_decode (ps : List Product) (hv : ∀ p ∈ ps, p.Valid) :
    ((scorePoints ps).1.map decode) = scoreValues (ps.map decodeProduct) := by
  have hc := criticalPoints_valid ps hv
  have hd := criticalPoints_decode ps hv
  simp only [scorePoints, List.map_append, FPTASCostLoops.cross_eq,
    List.filterMap_eq_map', List.map_flatMap, List.map_map, Function.comp_def]
  have hm : ((criticalPoints ps).1.flatMap
      (fun x => (criticalPoints ps).1.map (fun y => decode (midpoint x y).1))) =
      ((criticalPoints ps).1.map decode).flatMap
        (fun x => ((criticalPoints ps).1.map decode).map (fun y => (x+y)/2)) := by
    simp only [List.flatMap_map, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro x hx
    apply List.map_congr_left
    intro y hy
    exact midpoint_decode x y (hc x hx) (hc y hy)
  rw [hm, hd]
  rfl

end BalancedAssortments.FixedSupportCostPoints
