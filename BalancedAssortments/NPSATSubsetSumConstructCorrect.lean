import BalancedAssortments.NPSATSubsetSumLists

namespace BalancedAssortments.NPSATSubsetSum
open NPCNF NPCNF.Encoding ComplexityTimeBinary

lemma flatMap_indexed {α β : Type*} (xs : List α) (f : α → List β) :
    xs.flatMap f = (List.finRange xs.length).flatMap (fun i => f xs[i.val]) := by
  have h : (List.finRange xs.length).map (fun i => xs[i.val]) = xs := by
    rw [← List.ofFn_eq_map,List.ofFn_getElem]
  calc xs.flatMap f = ((List.finRange xs.length).map (fun i => xs[i.val])).flatMap f := congrArg (List.flatMap f) h.symm
       _ = _ := List.flatMap_map _ _ _

lemma flatMap_finRange_congr {α : Type*} {m n : ℕ} (h : m=n)
    (f : Fin m → List α) (g : Fin n → List α)
    (he : ∀ i,f i=g (Fin.cast h i)) :
    (List.finRange m).flatMap f=(List.finRange n).flatMap g := by
  subst n
  have hh : f=g := funext he
  rw [hh]

lemma basis_cast {m n : ℕ} (h : m=n) (i : Fin m) (a : ℕ) :
    List.ofFn (fun k => if k=i then a else 0)=
      List.ofFn (fun k => if k=Fin.cast h i then a else 0) := by subst n; rfl

lemma variableItems_refines (raw : Raw) (h : raw.decode.Valid) :
    (variableItems raw.catalog raw.formula raw.catalog).1.map value =
      (pairIndices raw.decode.catalog.length).map
        (fun x => itemValue (indexedFormula raw.decode h) (.inl x)) := by
  rw [variableItems_value,flatMap_indexed,pairIndices_flatMap,List.map_flatMap]
  simp only [List.map_cons,List.map_nil]
  apply flatMap_finRange_congr (by simp [Raw.decode])
  intro i
  congr 1
  · exact variableItem_refines raw h i false
  · congr 1
    exact variableItem_refines raw h i true

lemma slackItems_refines (raw : Raw) (h : raw.decode.Valid) :
    (packSlack (zeroColumns raw.catalog).1 (slackColumns raw.formula).1).1.map value =
      (pairIndices raw.decode.formula.length).map
        (fun x => itemValue (indexedFormula raw.decode h) (.inr x)) := by
  rw [packSlack_value]
  have hh : (slackColumns raw.formula).1.map (fun row => Nat.ofDigits 10
      (((zeroColumns raw.catalog).1++row).map value)) =
      (slackRows raw.formula.length).map (fun row => Nat.ofDigits 10 (List.replicate raw.catalog.length 0++row)) := by
    rw [← slackColumns_values raw.formula,List.map_map]
    simp only [Function.comp_def,List.map_append,zeroColumns_eq,List.map_replicate,value]
  rw [hh,slackRows_spec,List.map_flatMap,pairIndices_flatMap,List.map_flatMap]
  simp only [List.map_cons,List.map_nil]
  apply flatMap_finRange_congr (by simp [Raw.decode])
  intro j
  simp only [itemValue_slack,Bool.false_eq_true,↓reduceIte]
  have hn : raw.catalog.length=raw.decode.catalog.length := by simp [Raw.decode]
  have hm : raw.formula.length=raw.decode.formula.length := by simp [Raw.decode]
  rw [hn,basis_cast hm j 1,basis_cast hm j 2]

theorem construct_items (raw : Raw) (h : raw.decode.Valid) :
    (construct raw).1.2.map value = (itemEnumeration raw.decode.catalog.length raw.decode.formula.length).map
      (itemValue (indexedFormula raw.decode h)) := by
  simp only [construct,List.map_append,itemEnumeration,List.map_map,Function.comp_def]
  rw [variableItems_refines raw h,slackItems_refines raw h]

/-- Exact value-level correctness of the actual raw-bit constructor. -/
theorem construct_correct (raw : Raw) (h : raw.decode.Valid) (h3 : ThreeCNF raw.decode.formula) :
    raw.decode.Sat ↔ ListSubsetSum ((construct raw).1.2.map value) (value (construct raw).1.1) := by
  rw [construct_items raw h,construct_target]
  have he : targetValue raw.catalog.length raw.formula.length =
      targetValue raw.decode.catalog.length raw.decode.formula.length := by simp [Raw.decode]
  rw [he,← enumerated_sat_iff _ (indexedFormula_three raw.decode h h3)]
  exact catalog_sat_iff_indexed raw.decode h

end BalancedAssortments.NPSATSubsetSum
