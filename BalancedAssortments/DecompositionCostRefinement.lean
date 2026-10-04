import BalancedAssortments.DecompositionCostExecution
import BalancedAssortments.DecompositionCostInput
import BalancedAssortments.DecompositionCostSelection

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary CostBinary

theorem map_value_ofFn {n : ℕ} (x : Fin n → Bits) :
    (List.ofFn x).map value = List.ofFn (fun i => value (x i)) := by
  simp only [List.map_ofFn, Function.comp_def]

def maskFn {n : ℕ} (ms : List Bool) (i : Fin n) : Bool := ms[i.val]?.getD false

theorem mask_ofFn {n : ℕ} (ms : List Bool) (hlen : ms.length = n) :
    List.ofFn (maskFn (n := n) ms) = ms := by
  subst n
  convert List.ofFn_getElem ms using 2
  funext i
  simp [maskFn, List.getElem?_eq_getElem, i.isLt]

theorem maskFn_mem {n : ℕ} (ms : List Bool) (i : Fin n) :
    maskFn ms i = true ↔ i ∈ maskSet (n := n) ms := by
  simp [maskFn, maskSet]

theorem minimumNatMasked_ofFn {n : ℕ} (R : ℕ) (a : Fin n → ℕ) (b : Fin n → Bool) :
    minimumNatMasked R (List.ofFn a) (List.ofFn b) =
      (List.ofFn (fun i => if b i then a i else R-a i)).foldr min R := by
  induction n with
  | zero => simp [minimumNatMasked]
  | succ n ih => simp [List.ofFn_succ, minimumNatMasked, ih]

theorem subtractNatMasked_ofFn {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (b : Fin n → Bool) :
    subtractNatMasked m (List.ofFn a) (List.ofFn b) =
      List.ofFn (fun i => if b i then a i-m else a i) := by
  induction n with
  | zero => simp [subtractNatMasked]
  | succ n ih => simp [List.ofFn_succ, subtractNatMasked, ih]

theorem minimumNatMasked_grid {n : ℕ} (R : ℕ) (a : Fin n → ℕ) (ms : List Bool)
    (hlen : ms.length = n) :
    minimumNatMasked R (List.ofFn a) ms =
      (List.ofFn (gridStepBound R a (maskSet ms))).foldr min R := by
  conv_lhs => rw [← mask_ofFn ms hlen]
  rw [minimumNatMasked_ofFn]
  congr 2
  funext i
  simp only [gridStepBound]
  simp only [← maskFn_mem]

theorem subtractNatMasked_grid {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (ms : List Bool)
    (hlen : ms.length = n) :
    subtractNatMasked m (List.ofFn a) ms =
      List.ofFn (gridResidual a (maskSet ms) m) := by
  conv_lhs => rw [← mask_ofFn ms hlen]
  rw [subtractNatMasked_ofFn]
  congr 1
  funext i
  simp only [gridResidual]
  simp only [← maskFn_mem]

private theorem min_fold_le_mem (R x : ℕ) (xs : List ℕ) (hx : x ∈ xs) : xs.foldr min R ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hx)

private theorem le_min_fold (m R : ℕ) (xs : List ℕ) (hR : m ≤ R)
    (hx : ∀ x ∈ xs, m ≤ x) : m ≤ xs.foldr min R := by
  induction xs with
  | nil => exact hR
  | cons a xs ih => exact le_min (hx a (by simp)) (ih (fun x hx' => hx x (by simp [hx'])))

/-- The minimum over all coordinates equals the fractional-coordinate minimum:
integral coordinates contribute the harmless upper bound R. -/
theorem minimum_gridStep {n K R : ℕ} (a : Fin n → ℕ) (hR : 0 < R)
    (h : Feasible K (gridValues R a)) (hf : gridFractional R a ≠ ∅) :
    (List.ofFn (gridStepBound R a (gridSet K R a))).foldr min R =
      gridStep R a (gridSet K R a) := by
  let S := gridSet K R a
  let m := gridStep R a S
  have hS : PeelSet K (gridValues R a) S := by
    simpa [S, hR] using greedySet_valid h
  have hqf : (fractional (gridValues R a)).Nonempty := by
    simpa [hR] using Finset.nonempty_iff_ne_empty.mpr hf
  obtain ⟨_, ht1, hb, _, _, _⟩ := greedyStep_spec h hS hqf
  rw [greedyStep_gridValues hR a h S] at ht1 hb
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hm : m < R := by exact_mod_cast (div_lt_one hRq).mp ht1
  have ha : ∀ i, a i ≤ R := by
    intro i
    have hh := (h.1 i).2
    change (a i : ℚ) / R ≤ 1 at hh
    exact_mod_cast (div_le_one hRq).mp hh
  have hmb : ∀ i, m ≤ gridStepBound R a S i := by
    intro i
    have hh := hb i
    rw [stepBound_gridValues hR a ha S i] at hh
    exact_mod_cast (div_le_div_iff_of_pos_right hRq).mp hh
  apply le_antisymm
  · have hfn := Finset.nonempty_iff_ne_empty.mpr hf
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp
      (((gridFractional R a).image (gridStepBound R a S)).min'_mem (hfn.image _))
    have hmi : m = gridStepBound R a S i := by simp only [m, gridStep, dif_pos hfn]; exact he.symm
    rw [show gridStep R a (gridSet K R a) = m from rfl, hmi]
    apply min_fold_le_mem
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · apply le_min_fold _ _ _ hm.le
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hmb i


theorem allIntegral_grid {n : ℕ} (R : Bits) (x : Fin n → Bits) :
    (allIntegral (classify R (List.ofFn x)).1).1 = true ↔
      gridFractional (value R) (fun i => value (x i)) = ∅ := by
  simp [allIntegral_value, classify_value, List.map_ofFn,
    gridFractional, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi
    exact (h i).resolve_right hi
  · intro h i
    by_cases hi : value (x i) = 0
    · exact Or.inr hi
    · exact Or.inl (h hi)

theorem gridSet_zero {n R : ℕ} (a : Fin n → ℕ) : gridSet 0 R a = gridOnes R a := by
  simp [gridSet]

theorem gridSet_integral {n K R : ℕ} (a : Fin n → ℕ)
    (hf : gridFractional R a = ∅) : gridSet K R a = gridOnes R a := by
  have he : gridPositive a \ gridOnes R a = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hi' := Finset.mem_sdiff.mp hi
    have hpos : 0 < a i := (Finset.mem_filter.mp hi'.1).2
    have hn : a i ≠ R := by simpa [gridOnes] using hi'.2
    have hm : i ∈ gridFractional R a := by simp [gridFractional, hpos.ne', hn]
    rw [hf] at hm
    exact Finset.notMem_empty i hm
  simp [gridSet, he]


theorem selectMask_ofFn {n : ℕ} (K : ℕ) (R : Bits) (x : Fin n → Bits) :
    maskSet (selectMask K R (List.ofFn x)).1 =
      gridSet K (value R) (fun i => value (x i)) := by
  simpa [List.ofFn_eq_map] using selectMask_gridSet K R x

theorem minimumMasked_gridStep {n K : ℕ} (R : Bits) (x : Fin n → Bits)
    (hR : 0 < value R) (h : Feasible K (gridValues (value R) (fun i => value (x i))))
    (hf : gridFractional (value R) (fun i => value (x i)) ≠ ∅) :
    value (minimumMasked R (List.ofFn x) (selectMask K R (List.ofFn x)).1).1 =
      gridStep (value R) (fun i => value (x i)) (gridSet K (value R) (fun i => value (x i))) := by
  rw [minimumMasked_value, List.map_ofFn]
  rw [minimumNatMasked_grid _ _ _ (by simp), selectMask_ofFn]
  exact minimum_gridStep _ hR h hf

theorem subtractMasked_grid {n : ℕ} (m R : Bits) (x : Fin n → Bits) (K : ℕ) :
    ((subtractMasked m (List.ofFn x) (selectMask K R (List.ofFn x)).1).1.map value) =
      List.ofFn (gridResidual (fun i => value (x i))
        (gridSet K (value R) (fun i => value (x i))) (value m)) := by
  rw [subtractMasked_value, List.map_ofFn,
    subtractNatMasked_grid _ _ _ (by simp), selectMask_ofFn]
  rfl

theorem list_ofFn_getD {α : Type*} {n : ℕ} (xs : List α) (d : α) (hlen : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]?.getD d) = xs := by
  subst n
  convert List.ofFn_getElem xs using 2
  funext i
  simp [i.isLt]

/-- Semantics of one nonintegral residual step, needed for recursive refinement. -/
theorem grid_next_feasible {n K R : ℕ} (a : Fin n → ℕ) (hR : 0 < R)
    (h : Feasible K (gridValues R a)) (hf : gridFractional R a ≠ ∅) :
    let S := gridSet K R a
    let m := gridStep R a S
    0 < R-m ∧ Feasible K (gridValues (R-m) (gridResidual a S m)) := by
  let S := gridSet K R a
  let m := gridStep R a S
  have hS : PeelSet K (gridValues R a) S := by
    simpa [S, hR] using greedySet_valid h
  have hqf : (fractional (gridValues R a)).Nonempty := by
    simpa [hR] using Finset.nonempty_iff_ne_empty.mpr hf
  obtain ⟨_, ht1, hb, _, _, _⟩ := greedyStep_spec h hS hqf
  rw [greedyStep_gridValues hR a h S] at ht1 hb
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hm : m < R := by exact_mod_cast (div_lt_one hRq).mp ht1
  have hma : ∀ i ∈ S, m ≤ a i := by
    intro i hi
    have hh := hb i
    simp only [stepBound, hi, ↓reduceIte, gridValues] at hh
    exact_mod_cast (div_le_div_iff_of_pos_right hRq).mp hh
  refine ⟨Nat.sub_pos_of_lt hm, ?_⟩
  rw [gridResidual_values hR hm a S hma]
  exact residual_feasible h hS ht1 hb

def interpretBitAtoms {n : ℕ} (p : List BitAtom) : List (GridAtom n) :=
  p.map fun a => (value a.1, maskSet a.2)


/-- The executable binary loop returns exactly the integer-grid atoms. -/
theorem binaryGridAux_refines_ofFn {n : ℕ} (fuel K : ℕ) (R : Bits) (x : Fin n → Bits)
    (hR : 0 < value R) (h : Feasible K (gridValues (value R) (fun i => value (x i)))) :
    interpretBitAtoms (n := n) (binaryGridAux fuel K R (List.ofFn x)).1 =
      gridAux fuel K (value R) (fun i => value (x i)) := by
  induction fuel generalizing R x with
  | zero =>
    simp only [binaryGridAux, gridAux, interpretBitAtoms, List.map_cons, List.map_nil]
    rw [selectMask_ofFn, gridSet_zero]
  | succ fuel ih =>
    by_cases hf : gridFractional (value R) (fun i => value (x i)) = ∅
    · have hint := (allIntegral_grid R x).2 hf
      simp only [binaryGridAux, hint, ↓reduceIte, gridAux, hf, interpretBitAtoms,
        List.map_cons, List.map_nil]
      rw [selectMask_ofFn, gridSet_integral _ hf]
    · have hint : (allIntegral (classify R (List.ofFn x)).1).1 ≠ true :=
        fun hh => hf ((allIntegral_grid R x).1 hh)
      let S := gridSet K (value R) (fun i => value (x i))
      let m := gridStep (value R) (fun i => value (x i)) S
      let mb := (minimumMasked R (List.ofFn x) (selectMask K R (List.ofFn x)).1).1
      let R' := (subBits R mb).1
      let xs' := (subtractMasked mb (List.ofFn x) (selectMask K R (List.ofFn x)).1).1
      have hlen : xs'.length = n := by simp [xs']
      let x' : Fin n → Bits := fun i => xs'[i.val]?.getD []
      have hx' : List.ofFn x' = xs' := list_ofFn_getD xs' [] hlen
      have hm : value mb = m := minimumMasked_gridStep R x hR h hf
      have hR' : value R' = value R - m := by simp [R', subBits_value, hm]
      have hvals : (fun i => value (x' i)) = gridResidual (fun i => value (x i)) S m := by
        apply List.ofFn_injective
        rw [← map_value_ofFn, hx']
        change xs'.map value = _
        rw [show xs'.map value = List.ofFn (gridResidual (fun i => value (x i)) S (value mb)) from
          subtractMasked_grid mb R x K, hm]
      have hnext := grid_next_feasible (fun i => value (x i)) hR h hf
      have hi := ih R' x' (by rw [hR']; exact hnext.1)
        (by rw [hR', hvals]; exact hnext.2)
      rw [hR', hvals, hx'] at hi
      simp only [binaryGridAux, hint, ↓reduceIte, gridAux, if_neg hf,
        interpretBitAtoms, List.map_cons] at ⊢
      change (value mb, maskSet (selectMask K R (List.ofFn x)).1) ::
          interpretBitAtoms (binaryGridAux fuel K R' xs').1 =
        (m, S) :: gridAux fuel K (value R-m) (gridResidual (fun i => value (x i)) S m)
      rw [hm, selectMask_ofFn, hi]

/-- Arbitrary list representation version, used by the common-denominator initializer. -/
theorem binaryGridAux_refines {n : ℕ} (fuel K : ℕ) (R : Bits) (xs : List Bits)
    (a : Fin n → ℕ) (hxs : xs.map value = List.ofFn a)
    (hR : 0 < value R) (h : Feasible K (gridValues (value R) a)) :
    interpretBitAtoms (n := n) (binaryGridAux fuel K R xs).1 = gridAux fuel K (value R) a := by
  have hlen : xs.length = n := by simpa using congrArg List.length hxs
  let x : Fin n → Bits := fun i => xs[i.val]?.getD []
  have hx : List.ofFn x = xs := list_ofFn_getD xs [] hlen
  have hval : (fun i => value (x i)) = a := by
    apply List.ofFn_injective
    rw [← map_value_ofFn, hx, hxs]
  have hh := binaryGridAux_refines_ofFn fuel K R x hR (by rwa [hval])
  rwa [hx, hval] at hh


/-- Initialization and every binary iteration refine the proved integer-grid
algorithm, including the shared denominator and every support set. -/
theorem encoded_binaryGreedy_refines_grid {n K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) :
    (value (binaryGreedy K (encodedNumerators z) (encodedDenominators z)).1,
      interpretBitAtoms (n := n)
        (binaryGreedy K (encodedNumerators z) (encodedDenominators z)).2.1) =
      gridGreedy K z := by
  have hR : 0 < value (productBits (encodedDenominators z)).1 := by
    rw [encodedDenominators_value]
    exact commonDenominator_pos z
  have hg : Feasible K (gridValues (value (productBits (encodedDenominators z)).1)
      (initialGridCounts z)) := by
    rw [encodedDenominators_value, initialGridValues (fun i => (h.1 i).1)]
    exact h
  have hh := binaryGridAux_refines n K (productBits (encodedDenominators z)).1
    (initialBitsCounts (encodedDenominators z) 0 (encodedNumerators z)).1
    (initialGridCounts z) (encodedCounts_value z) hR hg
  rw [encodedDenominators_value] at hh
  apply Prod.ext
  · exact encodedDenominators_value z
  · simpa only [binaryGreedy, encodedNumerators_length, gridGreedy] using hh

/-- The actual polynomial-bit binary implementation produces exactly the
certified rational greedy decomposition under mathematical interpretation. -/
theorem encoded_binaryGreedy_eq_greedy {n K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) :
    interpretGrid (value (binaryGreedy K (encodedNumerators z) (encodedDenominators z)).1)
      (interpretBitAtoms (n := n)
        (binaryGreedy K (encodedNumerators z) (encodedDenominators z)).2.1) = greedy K z := by
  have hp := encoded_binaryGreedy_refines_grid h
  have hd := congrArg Prod.fst hp
  have ha := congrArg Prod.snd hp
  dsimp only at hd ha
  rw [hd, ha]
  exact gridGreedy_eq_greedy h

/-- Complete constructive decomposition guarantee in the explicit binary/list
cost model: exact rational marginals, legal displays, at most n+1 atoms, and a
polynomial bound in the bit length of the actual rational input. -/
theorem encoded_binaryGreedy_certified {n K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) (hK : K ≤ n) :
    let out := binaryGreedy K (encodedNumerators z) (encodedDenominators z)
    ValidDecomposition K z (interpretGrid (value out.1) (interpretBitAtoms (n := n) out.2.1)) ∧
      out.2.1.length ≤ n+1 ∧
      out.2.2 ≤ 8192 * (n+1)^2 * (inputRationalBits z + 1)^2 := by
  have he := encoded_binaryGreedy_eq_greedy h
  refine ⟨?_, ?_, encoded_binaryGreedy_bit_cost hK z⟩
  · rw [he]
    exact (greedy_correct h).1
  · have hl := (greedy_correct h).2
    rw [← he] at hl
    simpa [interpretGrid, interpretBitAtoms] using hl

end BalancedAssortments.Decomposition.CostMachine
