import BalancedAssortments.NPSATSubsetSumSlack

namespace BalancedAssortments.NPSATSubsetSum

/-- Index-sensitive Subset Sum over a list, preserving repeated item values. -/
def ListSubsetSum (items : List ℕ) (target : ℕ) : Prop :=
  ∃ selected : List ℕ,selected.Sublist items ∧ selected.sum=target

def pairIndices (n : ℕ) : List (Fin n × Bool) := (List.finRange n).product [false,true]
def itemEnumeration (n m : ℕ) : List (Item n m) :=
  (pairIndices n).map Sum.inl++(pairIndices m).map Sum.inr

lemma pairIndices_flatMap (n : ℕ) : pairIndices n = (List.finRange n).flatMap (fun i => [(i,false),(i,true)]) := rfl
lemma pairIndices_nodup (n : ℕ) : (pairIndices n).Nodup :=
  (List.nodup_finRange n).product (by decide)
lemma pairIndices_complete {n : ℕ} (x : Fin n × Bool) : x ∈ pairIndices n := by
  rcases x with ⟨i,b⟩
  cases b <;> simp [pairIndices]
lemma itemEnumeration_nodup (n m : ℕ) : (itemEnumeration n m).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨(pairIndices_nodup n).map Sum.inl_injective,(pairIndices_nodup m).map Sum.inr_injective,?_⟩
  simp [List.disjoint_left]
lemma itemEnumeration_complete {n m : ℕ} (x : Item n m) : x ∈ itemEnumeration n m := by
  cases x with
  | inl x => exact List.mem_append_left _ (List.mem_map.mpr ⟨x,pairIndices_complete x,rfl⟩)
  | inr x => exact List.mem_append_right _ (List.mem_map.mpr ⟨x,pairIndices_complete x,rfl⟩)

lemma itemEnumeration_length (n m : ℕ) : (itemEnumeration n m).length=2*(n+m) := by
  simp [itemEnumeration,pairIndices_flatMap,List.length_flatMap,List.map_const']
  omega

lemma enumerated_subset_sum_iff {I : Type*} [DecidableEq I] (items : List I)
    (hn : items.Nodup) (hc : ∀ i,i∈items) (a : I → ℕ) (B : ℕ) :
    ListSubsetSum (items.map a) B ↔ ∃ T : Finset I,(∑ i ∈ T,a i)=B := by
  constructor
  · rintro ⟨selected,hsub,he⟩
    obtain ⟨is,hi,rfl⟩ := List.sublist_map_iff.mp hsub
    refine ⟨is.toFinset,?_⟩
    rw [List.sum_toFinset a (hi.nodup hn)]
    exact he
  · rintro ⟨T,he⟩
    let chosen := items.filter (fun i => decide (i∈T))
    have hsub : chosen.Sublist items := List.filter_sublist
    have hset : chosen.toFinset=T := by ext i; simp [chosen,hc i]
    refine ⟨chosen.map a,hsub.map a,?_⟩
    rw [← List.sum_toFinset a (hsub.nodup hn),hset]
    exact he

theorem enumerated_sat_iff {n m : ℕ} (F : IndexedFormula n m) (hF : ∀ j,(F j).length≤3) :
    IndexedSat F ↔ ListSubsetSum ((itemEnumeration n m).map (itemValue F)) (targetValue n m) := by
  rw [enumerated_subset_sum_iff _ (itemEnumeration_nodup n m) itemEnumeration_complete]
  exact indexed_sat_iff_subset_sum F hF

end BalancedAssortments.NPSATSubsetSum
