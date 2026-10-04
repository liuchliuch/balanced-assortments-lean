import BalancedAssortments.ComplexityTimeMatrix
import BalancedAssortments.DecompositionCostInput

/-! Explicit signed rational-row denominator clearing via binary products.
No division, gcd, or canonical-rational arithmetic is invoked. -/
namespace BalancedAssortments.ComplexityTimeVerifier
open ComplexityTimeBinary Decomposition.CostMachine

/-- Clear all signed numerator fields against the product of the other denominator
fields. The bounded index is used only in structural list deletion. -/
def clearSigned (dens : List (List Bool)) : ℕ → List ZBits → List ZBits × ℕ
  | _, [] => ([],1)
  | i, x::xs =>
      let e := eraseAt i dens
      let d := productBits e.1
      let p := mulBits x.1 d.1
      let n := mulBits x.2 d.1
      let r := clearSigned dens (i+1) xs
      ((p.1,n.1)::r.1,e.2+d.2+p.2+n.2+r.2+8)

theorem clearSigned_length (dens : List (List Bool)) (i : ℕ) (nums : List ZBits) :
    (clearSigned dens i nums).1.length = nums.length := by
  induction nums generalizing i <;> simp [clearSigned, *]

theorem clearSigned_value (dens : List (List Bool)) (i : ℕ) (nums : List ZBits) :
    (clearSigned dens i nums).1.map zvalue =
      nums.mapIdx (fun j x => zvalue x * ((((dens.eraseIdx (i+j)).map value).prod : ℕ) : ℤ)) := by
  induction nums generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [clearSigned, List.map_cons, List.mapIdx_cons, ih]
    congr 1
    · simp [zvalue, mulBits_value, productBits_value, eraseAt_value]
      ring
    · simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem clearSigned_width {L : ℕ} (dens : List (List Bool)) (hd : bitVolume dens ≤ L)
    (i : ℕ) (nums : List ZBits) (hn : ∀ x ∈ nums, width x ≤ L) :
    ∀ x ∈ (clearSigned dens i nums).1, width x ≤ 4*L+1 := by
  induction nums generalizing i with
  | nil => simp [clearSigned]
  | cons x xs ih =>
    have hx := hn x (by simp)
    have hdW := productBits_length (eraseAt i dens).1
    have he := (eraseAt_volume i dens).trans hd
    have hpW := mulBits_length x.1 (productBits (eraseAt i dens).1).1
    have hnW := mulBits_length x.2 (productBits (eraseAt i dens).1).1
    intro y hy
    simp only [clearSigned, List.mem_cons] at hy
    rcases hy with rfl | hy
    · unfold width at *
      dsimp only at *
      omega
    · exact ih _ (fun z hz => hn z (by simp [hz])) y hy

/-- Uniform polynomial bit-operation cost for clearing an entire rational row.
Input volume includes all denominator bits; numerators have bounded width. -/
theorem clearSigned_cost {L : ℕ} (dens : List (List Bool)) (hd : bitVolume dens ≤ L)
    (i : ℕ) (nums : List ZBits) (hn : ∀ x ∈ nums, width x ≤ L) :
    (clearSigned dens i nums).2 ≤ nums.length*((dens.length+1)*(4*inputProductBudget L))+1 := by
  induction nums generalizing i with
  | nil => simp [clearSigned]
  | cons x xs ih =>
    have hx := hn x (by simp)
    have ht := ih (i+1) (fun z hz => hn z (by simp [hz]))
    have heC := eraseAt_cost i dens
    have heV := (eraseAt_volume i dens).trans hd
    have heL := eraseAt_length i dens
    have hdC := productBits_cost (eraseAt i dens).1 heV
    have hdW := productBits_length (eraseAt i dens).1
    have hpC := mulBits_cost x.1 (productBits (eraseAt i dens).1).1
    have hnC := mulBits_cost x.2 (productBits (eraseAt i dens).1).1
    have hW : (productBits (eraseAt i dens).1).1.length ≤ 2*L+1 := by omega
    have hP : x.1.length ≤ L := (le_max_left _ _).trans hx
    have hN : x.2.length ≤ L := (le_max_right _ _).trans hx
    have hdc : (productBits (eraseAt i dens).1).2 ≤ dens.length*inputProductBudget L+1 :=
      hdC.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ heL) 1)
    have hp : (mulBits x.1 (productBits (eraseAt i dens).1).1).2 ≤ inputProductBudget L := by
      dsimp [inputProductBudget]
      nlinarith [Nat.mul_self_le_mul_self hP]
    have hn' : (mulBits x.2 (productBits (eraseAt i dens).1).1).2 ≤ inputProductBudget L := by
      dsimp [inputProductBudget]
      nlinarith [Nat.mul_self_le_mul_self hN]
    simp only [clearSigned, List.length_cons]
    have hb : 16 ≤ inputProductBudget L := by
      unfold inputProductBudget
      have hs : 0 < (L+1)^2 := by positivity
      omega
    nlinarith [Nat.mul_le_mul_left dens.length hb]

private theorem map_eraseIdx_eq {α β : Type*} (f : α → β) (xs : List α) (i : ℕ) :
    (xs.eraseIdx i).map f = (xs.map f).eraseIdx i := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp [ih]

private theorem get_mul_prod_eraseIdx (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs[i]*(xs.eraseIdx i).prod = xs.prod := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have h := ih i (by simpa using hi)
      simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.prod_cons]
      nlinarith

private theorem prod_eraseIdx_ofFn {m : ℕ} (d : Fin m → ℕ) (hd : ∀ i, 0 < d i) (i : Fin m) :
    ((List.ofFn d).eraseIdx i.val).prod = ∏ j ∈ Finset.univ.erase i, d j := by
  apply Nat.eq_of_mul_eq_mul_left (hd i)
  have h := get_mul_prod_eraseIdx (List.ofFn d) i.val (by simpa using i.isLt)
  simpa [List.prod_ofFn, Finset.mul_prod_erase _ _ (Finset.mem_univ i)] using h

def rawDenominators {m : ℕ} (a : Fin m → ℚ) : List (List Bool) :=
  List.ofFn (fun i => (a i).den.bits)

def rawNumerators {m : ℕ} (a : Fin m → ℚ) : List ZBits :=
  List.ofFn (fun i => zencode (a i).num)

/-- Concrete bitwise clearing agrees exactly with the integer coefficients used
in the rational-polyhedron certificate proofs. -/
theorem clearRational_value {m : ℕ} (a : Fin m → ℚ) :
    (clearSigned (rawDenominators a) 0 (rawNumerators a)).1.map zvalue =
      List.ofFn (fun i => RationalClearing.clearedNumerator
        (fun j => (a j).num) (fun j => (a j).den) i) := by
  rw [clearSigned_value]
  apply List.ext_getElem (by simp [rawNumerators])
  intro k hk hk'
  have hkm : k < m := by simpa using hk'
  simp only [rawNumerators, List.getElem_mapIdx, List.getElem_ofFn, Nat.zero_add, zencode_value]
  rw [map_eraseIdx_eq]
  simp only [rawDenominators, List.map_ofFn, Function.comp_def, value_bits]
  rw [prod_eraseIdx_ofFn (fun j => (a j).den) (fun j => (a j).den_pos) ⟨k,hkm⟩]
  simp only [RationalClearing.clearedNumerator, Nat.cast_prod]

/-- Polynomial preprocessing cost from actual canonical input bit widths, including
all repeated product construction and signed numerator multiplication. -/
theorem clearRational_cost {m B : ℕ} (a : Fin m → ℚ)
    (ha : ∀ i, (a i).num.natAbs.size ≤ B ∧ (a i).den.size ≤ B) :
    (clearSigned (rawDenominators a) 0 (rawNumerators a)).2 ≤
      m*((m+1)*(4*inputProductBudget ((m+1)*(B+1))))+1 := by
  have hd : bitVolume (rawDenominators a) ≤ (m+1)*(B+1) := by
    unfold bitVolume rawDenominators
    rw [List.map_ofFn, List.sum_ofFn]
    have hh : (∑ i : Fin m, ((a i).den.bits).length) ≤ m*B := by
      calc (∑ i : Fin m, ((a i).den.bits).length) ≤ ∑ _i : Fin m, B :=
             Finset.sum_le_sum (fun i _ => by simpa only [Nat.size_eq_bits_len] using (ha i).2)
           _ = m*B := by simp
    simp only [Function.comp_def]
    nlinarith
  have hn : ∀ x ∈ rawNumerators a, width x ≤ (m+1)*(B+1) := by
    simp only [rawNumerators, List.forall_mem_ofFn_iff, zencode_width]
    intro i
    have hh := (ha i).1
    nlinarith
  simpa only [rawNumerators, rawDenominators, List.length_ofFn] using
    clearSigned_cost (rawDenominators a) hd 0 (rawNumerators a) hn

end BalancedAssortments.ComplexityTimeVerifier
