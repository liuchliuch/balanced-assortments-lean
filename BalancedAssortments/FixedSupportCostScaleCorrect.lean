import BalancedAssortments.FixedSupportCostScale
import BalancedAssortments.FixedSupportCandidateFeasibility

namespace BalancedAssortments.FixedSupportCostScale
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportAlgorithm

private theorem drop_finset {n : ℕ} (o : List (Fin n)) (ho : o.Perm (List.finRange n)) (k : ℕ) :
    (o.drop k).toFinset=Finset.univ\(o.take k).toFinset := by
  have hn := ho.nodup_iff.mpr (List.nodup_finRange n)
  have hd := List.disjoint_left.mp (List.disjoint_take_drop hn (le_refl k))
  ext i
  simp only [List.mem_toFinset,Finset.mem_sdiff,Finset.mem_univ,true_and]
  constructor
  · intro hi ht
    exact hd ht hi
  · intro hi
    have hm : i ∈ o := ho.mem_iff.mpr (List.mem_finRange i)
    rw [← List.take_append_drop k o,List.mem_append] at hm
    exact hm.resolve_left hi

theorem prefixRoot_list_formula {n : ℕ} (v : Fin n→ℚ) (α K a : ℚ)
    (o : List (Fin n)) (ho : o.Perm (List.finRange n)) (k : ℕ) :
    (K-(((o.take k).filter (fun i => decide (α*v i≤a))).length : ℚ)) /
      (((o.drop k).map (fun i => 1/v i)).sum+(1/α)*
        (((o.take k).filter (fun i => decide (¬α*v i≤a))).map (fun i => 1/v i)).sum) =
      prefixRoot v α K a (o.take k).toFinset := by
  have hn := ho.nodup_iff.mpr (List.nodup_finRange n)
  have ht : (o.take k).Nodup := hn.take
  have hd : (o.drop k).Nodup := hn.drop
  have hcf : ((o.take k).filter (fun i => decide (α*v i≤a))).toFinset=
      (o.take k).toFinset ∩ cappedAt v α a := by
    ext i
    simp [List.toFinset_filter,cappedAt]
  have huf : ((o.take k).filter (fun i => decide (¬α*v i≤a))).toFinset=
      (o.take k).toFinset \ cappedAt v α a := by
    ext i
    simp [List.toFinset_filter,cappedAt]
  have hc := List.toFinset_card_of_nodup (ht.filter (fun i => decide (α*v i≤a)))
  rw [hcf] at hc
  have hu := List.sum_toFinset (fun i => 1/v i) (ht.filter (fun i => decide (¬α*v i≤a)))
  rw [huf] at hu
  have hs := List.sum_toFinset (fun i => 1/v i) hd
  rw [drop_finset o ho k] at hs
  rw [← hc,← hu,← hs]
  rfl

private theorem raw_root_decoded_lists (α K a : Fraction) (ps ss : List Fraction)
    (hα : Valid α) (hK : Valid K) (ha : Valid a) (hp : ∀ v ∈ ps,Valid v) :
    decode (prefixRootBits α K a ps ss).1 =
      (decode K-(((ps.map decode).filter (fun x => decide (decode α*x≤decode a))).length : ℚ)) /
        (((ss.map decode).map (fun x => 1/x)).sum+(1/decode α)*
          ((((ps.map decode).filter (fun x => decide (¬decode α*x≤decode a))).map (fun x => 1/x)).sum)) := by
  rw [prefixRootBits_decode _ _ _ _ _ hα hK ha hp]
  simp only [List.filter_map,List.length_map,List.map_map,Function.comp_def]

theorem prefixRootBits_canonical {n : ℕ} (v : Fin n→ℚ) (o : List (Fin n))
    (ho : o.Perm (List.finRange n)) (xs : List Fraction) (α K a : Fraction) (k : ℕ)
    (hx : xs.map decode=o.map v) (hv : ∀ x ∈ xs,Valid x)
    (hα : Valid α) (hK : Valid K) (ha : Valid a) :
    decode (prefixRootBits α K a (xs.take k) (xs.drop k)).1 =
      prefixRoot v (decode α) (decode K) (decode a) (o.take k).toFinset := by
  have hp : ∀ x ∈ xs.take k,Valid x := fun x hm => hv x (List.mem_of_mem_take hm)
  rw [raw_root_decoded_lists _ _ _ _ _ hα hK ha hp]
  have ht : (xs.take k).map decode=(o.take k).map v := by
    rw [List.map_take,hx,List.map_take]
  have hd : (xs.drop k).map decode=(o.drop k).map v := by
    rw [List.map_drop,hx,List.map_drop]
  rw [ht,hd]
  simp only [List.filter_map,List.length_map,List.map_map,Function.comp_def]
  exact prefixRoot_list_formula v (decode α) (decode K) (decode a) o ho k

private theorem min_fold_finset (a : ℚ) (xs : List ℚ) :
    xs.foldl min a = (insert a xs.toFinset).min' (Finset.insert_nonempty _ _) := by
  rw [List.foldl_eq_foldr]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons,List.toFinset_cons]
    simpa only [List.toFinset_cons,Finset.insert_comm a x,ih] using
      (Finset.min'_insert x (insert a xs.toFinset) (Finset.insert_nonempty _ _)).symm

theorem scaleUpperBits_canonical {n : ℕ} (v : Fin n→ℚ) (o : List (Fin n))
    (ho : o.Perm (List.finRange n)) (xs : List Fraction) (K : Fraction)
    (hx : xs.map decode=o.map v) (hv : ∀ x ∈ xs,Valid x) (hK : Valid K) :
    decode (scaleUpperBits K xs).1=scaleUpper v (decode K) := by
  have hs : (xs.map (fun x => 1/decode x)).sum=inverseSum v := by
    have hh := congrArg (fun l : List ℚ => (l.map (fun x => 1/x)).sum) hx
    simp only [List.map_map,Function.comp_def] at hh
    exact hh.trans (FixedSupportAlgorithm.sum_order o ho _)
  rw [scaleUpperBits_decode _ _ hK hv,hs,hx,min_fold_finset]
  have hf : (o.map v).toFinset=Finset.univ.image v := by
    ext a
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi,h⟩;exact ⟨i,h⟩
    · rintro ⟨i,h⟩;exact ⟨i,ho.mem_iff.mpr (List.mem_finRange i),h⟩
  simp only [hf,scaleUpper]

theorem capCutBits_canonical {n : ℕ} (v : Fin n→ℚ) (o : List (Fin n))
    (ho : o.Perm (List.finRange n)) (xs : List Fraction) (α T : Fraction)
    (hx : xs.map decode=o.map v) (hv : ∀ x ∈ xs,Valid x) (hα : Valid α) (hT : Valid T) :
    ((capCutBits α T xs).1.map decode).toFinset=capCuts v (decode α) (decode T) := by
  rw [capCutBits_decode _ _ _ hα hT hv]
  have hm : xs.map (fun x => decode α*decode x)=o.map (fun i => decode α*v i) := by
    have hh := congrArg (fun l : List ℚ => l.map (fun x => decode α*x)) hx
    simpa only [List.map_map,Function.comp_def] using hh
  rw [hm]
  ext a
  simp only [List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,List.mem_filter,
    decide_eq_true_eq,List.mem_map,capCuts,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (h|h|⟨⟨i,hi,he⟩,hc⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨⟨i,he⟩,hc⟩)
  · rintro (h|h|⟨⟨i,he⟩,hc⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨⟨i,ho.mem_iff.mpr (List.mem_finRange i),he⟩,hc⟩)

end BalancedAssortments.FixedSupportCostScale
