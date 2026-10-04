import BalancedAssortments.ComplexityTimeClearing
import BalancedAssortments.ComplexityTimeFractions

namespace BalancedAssortments.ComplexityTimeVerifier
open ComplexityTimeBinary ComplexityTimeFractions
open scoped BigOperators

private theorem get_mul_prod_erase (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs[i]*(xs.eraseIdx i).prod = xs.prod := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hh := ih i (by simpa using hi)
      simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.prod_cons]
      nlinarith [hh]

private theorem erase_prod {m : ℕ} (d : Fin m → ℕ) (hd : ∀ i, 0 < d i) (i : Fin m) :
    ((List.ofFn d).eraseIdx i.val).prod = ∏ j ∈ Finset.univ.erase i, d j := by
  apply Nat.eq_of_mul_eq_mul_left (hd i)
  have hh := get_mul_prod_erase (List.ofFn d) i.val (by simpa using i.isLt)
  simpa [List.prod_ofFn, Finset.mul_prod_erase _ _ (Finset.mem_univ i)] using hh

/-- Actual denominator clearing of arbitrary unreduced raw fractions agrees
with the mathematical integer clearing construction. -/
theorem clearRaw_value {m : ℕ} (a : Fin m → Fraction) (ha : ∀ i, Valid (a i)) :
    (clearSigned ((List.ofFn a).map Fraction.den) 0 ((List.ofFn a).map Fraction.num)).1.map zvalue =
      List.ofFn (fun i => RationalClearing.clearedNumerator
        (fun j => zvalue (a j).num) (fun j => value (a j).den) i) := by
  rw [clearSigned_value]
  apply List.ext_getElem (by simp)
  intro k hk hk'
  have hkm : k < m := by simpa using hk'
  simp only [List.getElem_mapIdx, List.getElem_map, List.getElem_ofFn, Nat.zero_add]
  rw [← List.eraseIdx_map]
  simp only [List.map_map, List.map_ofFn, Function.comp_def]
  rw [erase_prod (fun j => value (a j).den) ha ⟨k,hkm⟩]
  simp only [RationalClearing.clearedNumerator, Nat.cast_prod]

private theorem zip_values (as bs : List ZBits) :
    (as.zip bs).map (fun v => zvalue v.1*zvalue v.2) =
      ((as.map zvalue).zip (bs.map zvalue)).map (fun v => v.1*v.2) := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih => cases bs <;> simp [ih]

/-- The row checker depends on represented integers, not canonical bit encodings. -/
theorem raw_row_holds {n : ℕ} (as : List ZBits) (A p : Fin n → ℤ) (b : ZBits) (q : ℤ)
    (ha : as.map zvalue = List.ofFn A) :
    RowHolds as (encodedNumerators p) b (zencode q) ↔
      (∑ j, A j*p j) ≤ zvalue b*q := by
  have hlen : as.length = n := by simpa using congrArg List.length ha
  have hp : (encodedNumerators p).map zvalue = List.ofFn p := by
    simp [encodedNumerators, List.map_ofFn, Function.comp_def]
  have hpLen : (encodedNumerators p).length = n := by simp [encodedNumerators]
  simp only [RowHolds, hpLen, hlen, true_and, zencode_value, and_self_left]
  rw [zip_values, ha, hp, zip_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

private theorem value_headD (xs : List ZBits) :
    zvalue (xs.headD zzero) = (xs.map zvalue).headD 0 := by
  cases xs <;> simp [zvalue, zzero, value]

/-- Acceptance of the concrete cleared raw-fraction row is exactly its original
rational inequality. No gcd, canonical denominator, or semantic oracle is used. -/
theorem checkRawCoefficientRow_correct {n : ℕ} (coeff : Fin n → Fraction) (rhs : Fraction)
    (hc : ∀ i, Valid (coeff i)) (hb : Valid rhs) (p : Fin n → ℤ) (q : ℤ) (hq : 0 < q) :
    let row := rhs :: List.ofFn coeff
    let cleared := (clearSigned (row.map Fraction.den) 0 (row.map Fraction.num)).1
    (checkCoefficientRow cleared.tail (encodedNumerators p) (cleared.headD zzero) (zencode q)).1 = true ↔
      (∑ j, decode (coeff j) * (p j : ℚ) / (q : ℚ)) ≤ decode rhs := by
  let a : Fin (n+1) → Fraction := Fin.cons rhs coeff
  let pn : Fin (n+1) → ℤ := fun i => zvalue (a i).num
  let dn : Fin (n+1) → ℕ := fun i => value (a i).den
  let C := RationalClearing.clearedNumerator pn dn
  let D := RationalClearing.commonDenominator dn
  have ha : ∀ i, Valid (a i) := by intro i; exact Fin.cases hb hc i
  have hdn : ∀ i, 0 < dn i := ha
  have hD : (0 : ℚ) < D := by exact_mod_cast RationalClearing.commonDenominator_pos dn hdn
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  let row := rhs :: List.ofFn coeff
  let cleared := (clearSigned (row.map Fraction.den) 0 (row.map Fraction.num)).1
  have hlist : List.ofFn a = row := by simp [a, row, List.ofFn_succ]
  have hclear : cleared.map zvalue = List.ofFn C := by
    simpa only [cleared, ← hlist] using clearRaw_value a ha
  have htail : cleared.tail.map zvalue = List.ofFn (fun i => C i.succ) := by
    rw [List.map_tail, hclear, List.ofFn_succ]
    rfl
  have hhead : zvalue (cleared.headD zzero) = C 0 := by
    rw [value_headD, hclear, List.ofFn_succ]
    rfl
  change (checkCoefficientRow cleared.tail (encodedNumerators p) (cleared.headD zzero) (zencode q)).1 = true ↔ _
  rw [checkCoefficientRow_correct, raw_row_holds _ _ p _ q htail, hhead]
  have he (i : Fin (n+1)) : (C i : ℚ) = (D : ℚ)*decode (a i) :=
    (RationalClearing.clearing_identity pn dn hdn i).symm
  have hint : ((∑ j, C j.succ*p j : ℤ) ≤ C 0*q) ↔
      (∑ j, (C j.succ : ℚ)*(p j : ℚ)) ≤ (C 0 : ℚ)*(q : ℚ) := by norm_cast
  rw [hint]
  simp_rw [he]
  have hsum : (∑ j, (D : ℚ)*decode (a j.succ)*(p j : ℚ)) =
      (D : ℚ)*(∑ j, decode (coeff j)*(p j : ℚ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [a, Fin.cons_succ]
    ring
  rw [hsum]
  change (D : ℚ)*(∑ j, decode (coeff j)*(p j : ℚ)) ≤ (D : ℚ)*decode rhs*(q : ℚ) ↔ _
  rw [mul_assoc, mul_le_mul_iff_right₀ hD, ← Finset.sum_div, div_le_iff₀ hq']

end BalancedAssortments.ComplexityTimeVerifier
