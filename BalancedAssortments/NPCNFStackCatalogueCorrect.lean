import BalancedAssortments.NPCNFStackCatalogueRun

namespace BalancedAssortments.NPCNF.StackCatalogue
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary
open Encoding (catalogFields)

lemma program_noChoice : NoChoice program := by
  have hout (q : Label Main) (a b : State) :
      (Macros.code macroCode q).rename id State.outer≠.choice a b :=
    rename_not_choice _ id State.outer (compile_noChoice macroCode .readTag input fresh q) a b
  have hmem (q : NPStackCatalogueMember.State) (a b : State) :
      (NPStackCatalogueMember.program.code q).rename (Sum.inl : NPStackCatalogueMember.Register → Register) State.member≠.choice a b :=
    rename_not_choice _ (Sum.inl : NPStackCatalogueMember.Register → Register) State.member (NPStackCatalogueMember.program_noChoice q) a b
  intro q a b
  cases q with
  | outer q =>
    cases q with
    | main q => cases q <;> simp only [program,code] <;> first | exact hout _ a b | simp
    | «local» q st => exact hout _ a b
  | member q =>
    cases q with
    | outer q =>
      cases q with
      | main q => cases q <;> simp only [program,code] <;> first | exact hmem _ a b | simp
      | «local» q st => exact hmem _ a b
    | equal f q => exact hmem _ a b

lemma program_deterministic : Deterministic program := noChoice_deterministic program_noChoice

lemma duplicate_record (label rest m : List Bool) (seen : List (List Bool)) (hin : value label∈seen.map value) :
    ∃ t ≤ recordCost label seen m,∃ d,
      Run program t
        (cfg .readTag (store (tagBits [true]++false::(tagBits label++false::rest)) m [] [] [] (dataFields seen) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  have hmem := member_call label rest m seen
  simp only [hin,decide_true] at hmem
  have hh := (header_call true (tagBits label++false::rest) m (dataFields seen)).trans
    ((read_label_call label rest m (dataFields seen)).trans (hmem.trans
      (.one (inspect_member true label rest m (dataFields seen)))))
  refine ⟨_,?_,_,hh,rfl⟩
  unfold recordCost
  omega

/-- Semantic duplicates, including distinct padded bit representations, are
rejected by a concrete finite run. -/
theorem reject_duplicates (labels seen : List (List Bool)) (rest m : List Bool)
    (hs : (seen.map value).Nodup) (hn : ¬(labels.map value++seen.map value).Nodup) :
    ∃ t ≤ catalogueCost labels seen m,∃ d,
      Run program t (cfg .readTag (store (dataFields (catalogFields labels)++rest) m [] [] [] (dataFields seen) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  induction labels generalizing seen m with
  | nil => simp_all
  | cons x xs ih =>
    by_cases hx : value x∈seen.map value
    · obtain ⟨t,ht,d,hr,hd⟩ := duplicate_record x (dataFields (catalogFields xs)++rest) m seen hx
      refine ⟨t,ht.trans (by unfold catalogueCost;omega),d,?_,hd⟩
      simpa [catalogFields,dataFields,List.append_assoc] using hr
    · have hs' : ((x::seen).map value).Nodup := by simpa using And.intro hx hs
      have hn' : ¬(xs.map value++(x::seen).map value).Nodup := by
        intro h
        apply hn
        have hh : (value x::(xs.map value++seen.map value)).Nodup := List.perm_middle.nodup_iff.mp h
        simpa using hh
      obtain ⟨t,ht,d,hr,hd⟩ := ih (x::seen) (chooseMaximum x m) hs' hn'
      have hh := (record_run x (dataFields (catalogFields xs)++rest) m seen hx).trans hr
      refine ⟨recordCost x seen m+t,by unfold catalogueCost;omega,d,?_,hd⟩
      simpa [catalogFields,dataFields,List.append_assoc] using hh

/-- All accepting executions on a catalogued header have exactly the certified
freshness output, with no late acceptance of a duplicate catalogue. -/
theorem accepting_result (labels : List (List Bool)) (rest : List Bool) {t : ℕ} {d : Config Register State}
    (hr : Run program t (cfg .readTag (store (dataFields (catalogFields labels)++rest) [] [] [] [] [] [] [] [])) d)
    (ha : accepts program d) :
    (labels.map value).Nodup ∧
      d=cfg .accept (store rest [] (addCarry (selectedMaximum labels []) [] true).1 [] [] (dataFields labels.reverse) [] [] []) ∧
      t=catalogueCost labels [] [] := by
  by_cases hn : (labels.map value).Nodup
  · have hh := catalogue_run labels [] rest [] (by simpa using hn)
    simp only [List.append_nil,dataFields,List.flatMap_nil] at hh
    have he := hh.halted_unique program_deterministic hr rfl ha
    exact ⟨hn,he.2.symm,he.1.symm⟩
  · obtain ⟨u,_,e,he,hh⟩ := reject_duplicates labels [] rest [] (by simp) (by simpa using hn)
    simp only [dataFields,List.flatMap_nil] at he
    exact False.elim (rejecting_run_excludes_acceptance program_deterministic he hh hr ha)

end BalancedAssortments.NPCNF.StackCatalogue
