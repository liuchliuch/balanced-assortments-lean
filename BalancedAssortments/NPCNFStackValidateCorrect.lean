import BalancedAssortments.NPCNFStackValidateGrammar
import BalancedAssortments.NPStackEmbeddingDeterministic

namespace BalancedAssortments.NPCNF.StackValidate
open NPStack NPStack.Macros
open NPStackFields (dataFields)
open ComplexityTimeBinary
open Encoding

lemma header_reject_code (q : StackCatalogue.State) (h : StackCatalogue.program.code q=.halt false) :
    program.code (.header q)=.halt false := by
  by_cases he : q=StackCatalogue.State.outer (.main .accept)
  · subst q;cases h
  · have hc : program.code (.header q)=(StackCatalogue.program.code q).rename headerMap State.header := by
      cases q with
      | outer q => cases q with
        | main q => cases q <;> simp_all [program,code]
        | «local» q st => rfl
      | member q => rfl
    rw [hc,h]
    rfl

lemma lift_header_reject (bits : List Bool) {t : ℕ} {e : Config StackCatalogue.Register StackCatalogue.State}
    (hr : Run StackCatalogue.program t (StackCatalogue.cfg .readTag (StackCatalogue.store bits [] [] [] [] [] [] [] [])) e)
    (hh : StackCatalogue.program.code e.pc=.halt false) :
    ∃ d,Run program t ⟨.header (.outer (.main .readTag)),store bits [] [] [] [] [] []⟩ d ∧ program.code d.pc=.halt false := by
  have hrel : Relocated headerMap State.header
      (StackCatalogue.cfg .readTag (StackCatalogue.store bits [] [] [] [] [] [] [] []))
      ⟨.header (.outer (.main .readTag)),store bits [] [] [] [] [] []⟩ := by
    refine ⟨rfl,?_⟩
    intro k;cases k with
    | inl r => cases r <;> rfl
    | inr r => cases r <;> rfl
  obtain ⟨d,hd,he,_⟩ := hr.relocate headerMap State.header headerMap_injective header_extends hrel
  refine ⟨d,hd,?_⟩
  rw [he.1]
  exact header_reject_code e.pc hh

/-- Total semantic soundness of the concrete preparation pass. Every accepted
parsed field stream is exactly a valid original CNF encoding, with preserved
formula bytes, a duplicate-free raw catalogue, and certified fresh labels. -/
theorem prepare_accepting_result (fs : List (List Bool)) {T : ℕ} {d : Config Register State}
    (hr : Run program T ⟨.header (.outer (.main .readTag)),store (dataFields fs) [] [] [] [] [] []⟩ d)
    (ha : accepts program d) :
    ∃ raw : Raw,(pack fs).1=some raw ∧ raw.decode.Valid ∧ fields raw=fs ∧
      d=cfg .accept (store [] (dataFields (formulaFields raw.formula)) (freshBits raw.catalog)
        (dataFields raw.catalog.reverse) [] [] []) ∧ T=preparationCost raw := by
  cases hp : (parseCatalog fs).1 with
  | none =>
    obtain ⟨t,e,he,hh⟩ := StackCatalogue.reject_parseCatalog fs [] [] hp
    obtain ⟨e',he',hh'⟩ := lift_header_reject (dataFields fs) he hh
    exact False.elim (rejecting_run_excludes_acceptance program_deterministic he' hh' hr ha)
  | some p =>
    rcases p with ⟨labels,suffix⟩
    have hfields := Encoding.parseCatalog_sound fs labels suffix hp
    have hinput : dataFields fs=dataFields (catalogFields labels)++dataFields suffix := by
      rw [←hfields];simp [dataFields,List.flatMap_append]
    by_cases hn : (labels.map value).Nodup
    · have hhead := header_run labels (dataFields suffix) hn
      rw [←hinput] at hhead
      have hprefix := hhead.trans (save_formula_call (dataFields suffix) (freshBits labels) (dataFields labels.reverse))
      obtain ⟨u,ht,hu⟩ := (hprefix.deterministic program_noChoice).factor_halted hr ha
      obtain ⟨formula,hparse,hm,hfinal,huCost⟩ := formula_accepting_result suffix labels.reverse (dataFields suffix) (freshBits labels) hu ha
      have hformula : formulaFields formula=suffix := by
        simpa using Encoding.parseFormula_sound suffix suffix formula [] hparse
      let raw : Raw := ⟨labels,formula⟩
      have hlength : formula.length+1 ≤ fs.length := by
        have he := congrArg List.length hfields
        rw [←hformula,List.length_append,formulaFields_length] at he
        omega
      have hparse' : (parseFormula fs suffix).1=some (formula,[]) := by
        have hh := parseFormula_fields formula [] fs hlength
        simpa only [List.append_nil,hformula] using hh
      have hvalid : raw.decode.Valid := by
        refine ⟨hn,?_⟩
        intro c hc l hl
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
        obtain ⟨l',hl',rfl⟩ := List.mem_map.mp hl
        simpa [raw,Raw.decode,BitLiteral.decode,List.map_reverse] using hm c' hc' l' hl'
      refine ⟨raw,?_,hvalid,?_,?_,?_⟩
      · simp [pack,hp,hparse',raw]
      · change catalogFields labels++formulaFields formula=fs
        rw [hformula];exact hfields
      · simpa [raw,hformula] using hfinal
      · unfold preparationCost
        dsimp only [raw,Raw.catalog,Raw.formula]
        rw [hformula]
        omega
    · obtain ⟨t,_,e,he,hh⟩ := StackCatalogue.reject_duplicates labels [] (dataFields suffix) [] (by simp) (by simpa using hn)
      simp only [dataFields,List.flatMap_nil] at he
      change Run StackCatalogue.program t
        (StackCatalogue.cfg .readTag (StackCatalogue.store (dataFields (catalogFields labels)++dataFields suffix) [] [] [] [] [] [] [] [])) e at he
      rw [←hinput] at he
      obtain ⟨e',he',hh'⟩ := lift_header_reject (dataFields fs) he hh
      exact False.elim (rejecting_run_excludes_acceptance program_deterministic he' hh' hr ha)

end BalancedAssortments.NPCNF.StackValidate
