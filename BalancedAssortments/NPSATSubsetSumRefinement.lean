import BalancedAssortments.NPSATSubsetSumConstruct

namespace BalancedAssortments.NPSATSubsetSum
open NPCNF NPCNF.Encoding ComplexityTimeBinary

lemma catalogIndex_eq_iff (catalog : List ℕ) (hn : catalog.Nodup) (v : ℕ) (hv : v ∈ catalog)
    (i : Fin catalog.length) : catalogIndex catalog v hv=i ↔ v=catalog[i.val] := by
  constructor
  · intro h
    have hh := catalogIndex_get catalog v hv
    rw [h] at hh
    exact hh.symm
  · intro h
    apply Fin.ext
    simp only [catalogIndex]
    rw [h,List.idxOf_getElem hn]

lemma indexedClause_count (catalog : List ℕ) (hn : catalog.Nodup) (c : Clause)
    (hc : ∀ l ∈ c,l.var∈catalog) (i : Fin catalog.length) (b : Bool) :
    (indexedClause catalog c hc).count (i,b) =
      c.countP (fun l => decide (l.var=catalog[i.val] ∧ l.positive=b)) := by
  simp only [indexedClause,List.count,List.countP_map,Function.comp_def]
  calc
    _ = c.attach.countP (fun l => decide (l.val.var=catalog[i.val] ∧ l.val.positive=b)) := by
      apply List.countP_congr
      intro l hl
      simp only [beq_iff_eq,Prod.mk.injEq,catalogIndex_eq_iff catalog hn,decide_eq_true_eq]
    _ = _ := @List.countP_attach Literal c (fun l => decide (l.var=catalog[i.val] ∧ l.positive=b))

lemma digit_list_split {n m : ℕ} (f : Column n m → ℕ) :
    List.ofFn (fun i : Fin (n+m) => f (finSumFinEquiv.symm i)) =
      List.ofFn (fun i => f (.inl i))++List.ofFn (fun j => f (.inr j)) := by
  rw [List.ofFn_add]
  congr 1 <;> apply congrArg List.ofFn <;> funext i
  · have he : i.castLE (Nat.le_add_right n m)=i.castAdd m := rfl
    rw [he,finSumFinEquiv_symm_apply_castAdd]
  · rw [finSumFinEquiv_symm_apply_natAdd]

lemma variable_digit_eq {n m : ℕ} (F : IndexedFormula n m) (i k : Fin n) (b : Bool) :
    digit F (.inl (i,b)) (.inl k) = if k=i then 1 else 0 := by
  cases b <;> by_cases h : k=i <;> simp_all [digit,eq_comm]

lemma itemValue_variable {n m : ℕ} (F : IndexedFormula n m) (i : Fin n) (b : Bool) :
    itemValue F (.inl (i,b)) = Nat.ofDigits 10
      (List.ofFn (fun k => if k=i then 1 else 0)++List.ofFn (fun j => (F j).count (i,b))) := by
  simp only [itemValue,pack,digit_list_split]
  congr 1
  congr 1
  · apply congrArg List.ofFn; funext k; exact variable_digit_eq F i k b

lemma decoded_catalog_injective (raw : Raw) (h : raw.decode.Valid) :
    Function.Injective (fun i : Fin raw.catalog.length => value raw.catalog[i.val]) := by
  intro i j hij
  have hn : (raw.catalog.map value).Nodup := h.1
  have he : (raw.catalog.map value)[i.val]'(by simpa using i.isLt) =
      (raw.catalog.map value)[j.val]'(by simpa using j.isLt) := by simpa using hij
  have hh := (hn.getElem_inj_iff).mp he
  exact Fin.ext hh

/-- Literal digit values of the actual variable-item constructor agree with the
catalog-indexed semantic gadget, with no canonicalization of input labels. -/
theorem variableItem_refines (raw : Raw) (h : raw.decode.Valid)
    (i : Fin raw.catalog.length) (b : Bool) :
    value (variableItem raw.catalog raw.formula raw.catalog[i.val] b).1 =
      itemValue (indexedFormula raw.decode h) (.inl (⟨i.val,by simpa [Raw.decode] using i.isLt⟩,b)) := by
  rw [variableItem_value,itemValue_variable]
  congr 1
  congr 1
  · rw [← List.ofFn_getElem_eq_map]
    simp only [Raw.decode,List.length_map]
    apply congrArg List.ofFn
    funext k
    have he : value raw.catalog[k.val]=value raw.catalog[i.val] ↔ k=i :=
      (decoded_catalog_injective raw h).eq_iff
    simp only [he,Fin.ext_iff,Fin.coe_cast]
  · rw [← List.ofFn_getElem_eq_map]
    simp only [Raw.decode,List.length_map]
    apply congrArg List.ofFn
    funext j
    unfold indexedFormula
    dsimp only
    have hn : (raw.catalog.map value).Nodup := h.1
    rw [indexedClause_count _ hn]
    simp only [Raw.decode,List.getElem_map,List.countP_map,Function.comp_def,
      BitLiteral.decode,occurrenceCount,Fin.coe_cast]

end BalancedAssortments.NPSATSubsetSum
