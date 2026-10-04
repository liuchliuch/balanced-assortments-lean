import BalancedAssortments.NPSATSubsetSumRefinement

namespace BalancedAssortments.NPSATSubsetSum
open NPCNF NPCNF.Encoding ComplexityTimeBinary

def slackRows : ℕ → List (List ℕ)
  | 0 => []
  | n+1 => (1::List.replicate n 0)::(2::List.replicate n 0)::(slackRows n).map (0::·)

lemma slackColumns_values {α : Type*} (xs : List α) :
    ((slackColumns xs).1.map (List.map value)) = slackRows xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [slackColumns,List.map_cons,zeroColumns_eq,prependZero_eq,List.map_map,
      List.length_cons,slackRows]
    simp only [List.map_replicate,value,Bool.toNat_true,Bool.toNat_false]
    norm_num only
    congr 2
    simpa only [List.map_map,Function.comp_def,List.map_cons,value] using congrArg (List.map (0::·)) ih

lemma basis_head (n a : ℕ) :
    List.ofFn (fun k : Fin (n+1) => if k=0 then a else 0) = a::List.replicate n 0 := by
  rw [List.ofFn_succ]
  simp

lemma basis_succ {n : ℕ} (i : Fin n) (a : ℕ) :
    List.ofFn (fun k : Fin (n+1) => if k=i.succ then a else 0) =
      0::List.ofFn (fun k => if k=i then a else 0) := by
  rw [List.ofFn_succ]
  simp [Ne.symm (Fin.succ_ne_zero i)]

lemma slackRows_spec (n : ℕ) : slackRows n = (List.finRange n).flatMap (fun j =>
    [List.ofFn (fun k => if k=j then 1 else 0),List.ofFn (fun k => if k=j then 2 else 0)]) := by
  induction n with
  | zero => simp [slackRows]
  | succ n ih =>
    rw [slackRows,List.finRange_succ]
    simp only [List.flatMap_cons,basis_head,List.cons_append,List.nil_append,List.flatMap_map,
      Function.comp_def,basis_succ]
    rw [ih,List.map_flatMap]
    simp only [List.map_cons,List.map_nil]

lemma itemValue_slack {n m : ℕ} (F : IndexedFormula n m) (j : Fin m) (b : Bool) :
    itemValue F (.inr (j,b)) = Nat.ofDigits 10
      (List.replicate n 0++List.ofFn (fun k => if k=j then (if b then 2 else 1) else 0)) := by
  simp only [itemValue,pack,digit_list_split]
  congr 1
  congr 1
  · simp [digit]
  · apply congrArg List.ofFn
    funext k
    cases b <;> by_cases he : k=j <;> simp_all [digit,variableContribution,eq_comm]

lemma targetValue_list (n m : ℕ) : targetValue n m =
    Nat.ofDigits 10 (List.replicate n 1++List.replicate m 4) := by
  unfold targetValue pack
  rw [digit_list_split]
  simp [targetDigit,List.ofFn_const]

lemma construct_target (raw : Raw) : value (construct raw).1.1 =
    targetValue raw.catalog.length raw.formula.length := by
  simp [construct,packBits_value,targetColumns,List.map_append,List.map_map,
    Function.comp_def,value,List.map_const',targetValue_list]

end BalancedAssortments.NPSATSubsetSum
