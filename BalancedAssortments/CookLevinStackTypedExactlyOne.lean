import BalancedAssortments.CookLevinStackTypedLogic

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF

lemma negative_pair_holds (σ : Assignment) (e f) (a b : E) :
    fholds σ (Typed.clause [(a,false),(b,false)]) e f ↔
      ¬(σ (denote e a)=true ∧ σ (denote e b)=true) := by
  simp only [fholds_typed_clause,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,
    exists_eq_left,evalLiteral_false,Bool.not_eq_true]
  cases σ (denote e a) <;> cases σ (denote e b) <;> decide

lemma fixedExactlyOne_character (σ : Assignment) (e f) (es : List E) :
    fholds σ (Typed.fixedExactlyOne es) e f ↔
      (∃ a∈es,σ (denote e a)=true) ∧
      ∀ pair∈es.zipIdx,∀ b∈es.drop (pair.2+1),¬(σ (denote e pair.1)=true ∧ σ (denote e b)=true) := by
  rw [Typed.fixedExactlyOne,fholds_seq]
  constructor
  · rintro ⟨ha,hb⟩
    constructor
    · obtain ⟨l,hl,hval⟩ := (fholds_typed_clause _ _ _ _).mp ha
      obtain ⟨a,ham,rfl⟩ := List.mem_map.mp hl
      exact ⟨a,ham,by simpa using hval⟩
    · intro pair hp b hb'
      apply (negative_pair_holds _ _ _ _ _).mp
      apply (fholds_all _ _ _ _).mp hb
      exact List.mem_flatMap.mpr ⟨pair,hp,List.mem_map.mpr ⟨b,hb',rfl⟩⟩
  · rintro ⟨ha,hb⟩
    constructor
    · obtain ⟨a,ha,hval⟩ := ha
      apply (fholds_typed_clause _ _ _ _).mpr
      exact ⟨(a,true),List.mem_map.mpr ⟨a,ha,rfl⟩,by simpa using hval⟩
    · apply (fholds_all _ _ _ _).mpr
      intro c hc
      obtain ⟨pair,hp,hm⟩ := List.mem_flatMap.mp hc
      obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hm
      exact (negative_pair_holds _ _ _ _ _).mpr (hb pair hp b hb')

lemma zip_drop_pair_iff {α : Type*} (es : List α) (P : α → Prop) :
    (∀ pair∈es.zipIdx,∀ b∈es.drop (pair.2+1),¬(P pair.1 ∧ P b)) ↔
      ∀ i j : Fin es.length,i.val<j.val → ¬(P es[i.val] ∧ P es[j.val]) := by
  constructor
  · intro h i j hij
    apply h (es[i.val],i.val)
    · rw [List.mk_mem_zipIdx_iff_getElem?]
      exact List.getElem?_eq_getElem i.isLt
    · rw [List.mem_drop_iff_getElem]
      refine ⟨j.val-(i.val+1),by omega,?_⟩
      simp only [show i.val+1+(j.val-(i.val+1))=j.val by omega]
  · intro h pair hp b hb
    obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hp)
    obtain ⟨j,hj,hbe⟩ := List.mem_drop_iff_getElem.mp hb
    have hh := h ⟨pair.2,hi⟩ ⟨pair.2+1+j,by omega⟩ (by simp;omega)
    simpa only [he,hbe] using hh

lemma unique_of_ordered_pairs {α : Type*} (es : List α) (P : α → Prop) :
    ((∃ a∈es,P a) ∧ ∀ i j : Fin es.length,i.val<j.val → ¬(P es[i.val] ∧ P es[j.val])) ↔
      ∃ i : Fin es.length,P es[i.val] ∧ ∀ j : Fin es.length,P es[j.val] → j=i := by
  constructor
  · rintro ⟨⟨a,ha,hpa⟩,hp⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ha
    refine ⟨⟨i,hi⟩,by simpa [he] using hpa,?_⟩
    intro j hj
    apply Fin.ext
    by_contra hne
    change j.val≠i at hne
    by_cases hlt : i<j.val
    · exact hp ⟨i,hi⟩ j hlt ⟨by simpa [he] using hpa,hj⟩
    · exact hp j ⟨i,hi⟩ (by simp;omega) ⟨hj,by simpa [he] using hpa⟩
  · rintro ⟨i,hi,hu⟩
    refine ⟨⟨es[i.val],List.getElem_mem _,hi⟩,?_⟩
    intro j k hjk hboth
    have hj := hu j hboth.1
    have hk := hu k hboth.2
    subst j;subst k
    omega

theorem fixedExactlyOne_holds (σ : Assignment) (e f) (es : List E) :
    fholds σ (Typed.fixedExactlyOne es) e f ↔
      ∃ i : Fin es.length,σ (denote e es[i.val])=true ∧
        ∀ j : Fin es.length,σ (denote e es[j.val])=true → j=i := by
  rw [fixedExactlyOne_character,zip_drop_pair_iff es (fun a => σ (denote e a)=true)]
  exact unique_of_ordered_pairs es (fun a => σ (denote e a)=true)

theorem fixedExactlyOne_range (σ : Assignment) (e f) (n : ℕ) (a : ℕ → E) :
    fholds σ (Typed.fixedExactlyOne ((List.range n).map a)) e f ↔
      ∃ i : Fin n,σ (denote e (a i.val))=true ∧
        ∀ j : Fin n,σ (denote e (a j.val))=true → j=i := by
  rw [fixedExactlyOne_holds]
  simp only [List.getElem_map,List.getElem_range]
  constructor
  · rintro ⟨i,hi,hu⟩
    refine ⟨⟨i.val,by simpa using i.isLt⟩,hi,?_⟩
    intro j hj
    have hh := hu ⟨j.val,by simpa using j.isLt⟩ hj
    have hv := congrArg (fun k : Fin (List.map a (List.range n)).length => k.val) hh
    exact Fin.ext hv
  · rintro ⟨i,hi,hu⟩
    refine ⟨⟨i.val,by simpa using i.isLt⟩,hi,?_⟩
    intro j hj
    have hh := hu ⟨j.val,by simpa using j.isLt⟩ hj
    have hv := congrArg (fun k : Fin n => k.val) hh
    exact Fin.ext hv

end BalancedAssortments.CookLevin.StackTableau
