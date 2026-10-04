import BalancedAssortments.FixedSupportCostOrder
import BalancedAssortments.FixedSupportCostScaleCorrect
import BalancedAssortments.FixedSupportCostScaleList

namespace BalancedAssortments.FixedSupportCostScaleList
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints FixedSupportCostScalars FixedSupportCostScale
open FixedSupportAlgorithm

private theorem raw_scale_membership (α K : Fraction) (xs : List Fraction) (z : ℚ)
    (hα : Valid α) (hK : Valid K) (hv : ∀ x ∈ xs,Valid x) :
    z ∈ ((scalePoints α K xs).1.map decode).toFinset ↔
      z ∈ ((capCutBits α (scaleUpperBits K xs).1 xs).1.map decode).toFinset ∨
      ∃ a ∈ (capCutBits α (scaleUpperBits K xs).1 xs).1,
        ∃ p ∈ (prefixSplits xs).1,
          decode (prefixRootBits α K a p.1 p.2).1=z ∧ 0≤z ∧ z≤decode (scaleUpperBits K xs).1 := by
  have hu := scaleUpperBits_valid K xs hK hv
  simp only [List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨x,hx,rfl⟩
    rcases List.mem_append.mp hx with hc | hr
    · exact Or.inl ⟨x,hc,rfl⟩
    · have hh := List.mem_filter.mp (by simpa only [filterCost_value] using hr)
      have hroot := hh.1
      rw [FPTASCostLoops.cross_eq] at hroot
      obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hroot
      obtain ⟨p,hp,he⟩ := List.mem_filterMap.mp hp
      have hxv : Valid x := by
        rw [← Option.some.inj he]
        exact prefixRootBits_valid _ _ _ _ _ hK
      have hw := (within_correct _ _ hu hxv).mp hh.2
      exact Or.inr ⟨a,ha,p,hp,congrArg decode (Option.some.inj he),hw⟩
  · rintro (⟨x,hx,he⟩ | ⟨a,ha,p,hp,he,hz⟩)
    · exact ⟨x,List.mem_append_left _ hx,he⟩
    · refine ⟨(prefixRootBits α K a p.1 p.2).1,List.mem_append_right _ ?_,he⟩
      rw [filterCost_value]
      apply List.mem_filter.mpr
      constructor
      · rw [FPTASCostLoops.cross_eq]
        exact List.mem_flatMap.mpr ⟨a,ha,List.mem_filterMap.mpr ⟨p,hp,rfl⟩⟩
      · exact (within_correct _ _ hu (prefixRootBits_valid _ _ _ _ _ hK)).mpr (by simpa [he] using hz)

theorem scalePoints_canonical {n : ℕ} (r v : Fin n→ℚ) (ρ : ℚ)
    (xs : List Fraction) (α K : Fraction)
    (hx : xs.map decode=(scoreOrder r v ρ).map v)
    (hv : ∀ x ∈ xs,Valid x) (hα : Valid α) (hK : Valid K) :
    ((scalePoints α K xs).1.map decode).toFinset=
      scaleSamples r v (decode α) (decode K) ρ := by
  let o := scoreOrder r v ρ
  let T := (scaleUpperBits K xs).1
  let cuts := (capCutBits α T xs).1
  have ho := scoreOrder_perm r v ρ
  have hT : decode T=scaleUpper v (decode K) := scaleUpperBits_canonical v o ho xs K hx hv hK
  have hTv : Valid T := scaleUpperBits_valid K xs hK hv
  have hc : (cuts.map decode).toFinset=capCuts v (decode α) (scaleUpper v (decode K)) := by
    simpa only [hT] using capCutBits_canonical v o ho xs α T hx hv hα hTv
  have hcv : ∀ a ∈ cuts,Valid a := capCutBits_valid α T xs hα hTv hv
  have hlen : xs.length=n := by
    have hh := congrArg List.length hx
    have hl := ho.length_eq
    simp only [List.length_map,List.length_finRange] at hh hl
    omega
  ext z
  rw [raw_scale_membership α K xs z hα hK hv]
  change (z ∈ (cuts.map decode).toFinset ∨ _) ↔ _
  rw [hc]
  simp only [scaleSamples,Finset.mem_union,Finset.mem_filter]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨a,ha,p,hp,he,hz0,hzT⟩
    have hp' := prefixSplits_characterization xs hp
    have hkn : p.1.length≤n := by
      have hh := congrArg List.length (prefixSplits_append xs p hp)
      simp only [List.length_append,hlen] at hh
      omega
    have hr := prefixRootBits_canonical v o ho xs α K a p.1.length hx hv hα hK (hcv a ha)
    rw [← hp'.1,← hp'.2] at hr
    refine ⟨Finset.mem_image.mpr ⟨(decode a,p.1.length),?_,hr.symm.trans he⟩,hz0,?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · rw [← hc]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)
      · exact Finset.mem_range.mpr (by omega)
    · simpa only [← hT] using hzT
  · rintro ⟨hz,hz0,hzT⟩
    obtain ⟨ak,hak,he⟩ := Finset.mem_image.mp hz
    have hak' := Finset.mem_product.mp hak
    have hk : ak.2≤xs.length := by
      have hh := Finset.mem_range.mp hak'.2
      omega
    have ha : ak.1 ∈ (cuts.map decode).toFinset := by rw [hc];exact hak'.1
    obtain ⟨a,ha,hav⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hr := prefixRootBits_canonical v o ho xs α K a ak.2 hx hv hα hK (hcv a ha)
    refine ⟨a,ha,(xs.take ak.2,xs.drop ak.2),prefixSplits_take_drop xs ak.2 hk,?_,hz0,?_⟩
    · exact hr.trans (by simpa only [hav] using he)
    · change z≤decode T
      rw [hT]
      exact hzT

theorem ordered_scalePoints_canonical {n : ℕ} (r v : Fin n→ℚ)
    (ps : List (Fin n×Product)) (ρ α K : Fraction)
    (hlabels : ps.map Prod.fst=List.finRange n) (hp : ∀ p ∈ ps,p.2.Valid)
    (hρ : Valid ρ) (hα : Valid α) (hK : Valid K)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1) :
    ((scalePoints α K ((FixedSupportCostOrder.ordered ps ρ).1.map (fun s => s.product.2))).1.map decode).toFinset =
      scaleSamples r v (decode α) (decode K) (decode ρ) := by
  have ho := FixedSupportCostOrder.ordered_labels r v ps ρ hlabels hp hρ hdata
  apply scalePoints_canonical r v (decode ρ) _ α K _ _ hα hK
  · rw [← ho]
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro s hs
    exact (hdata _ (FixedSupportCostOrder.ordered_member ps ρ hs).1).2
  · intro x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    exact (FixedSupportCostOrder.ordered_valid ps ρ hp hρ s hs).1.2

end BalancedAssortments.FixedSupportCostScaleList
