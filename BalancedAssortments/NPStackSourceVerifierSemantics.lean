import BalancedAssortments.NPStackSourceVerifierFinalState
import BalancedAssortments.DirectVerifierStreamingSource

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

def semanticConditions (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) : Prop :=
  let e := (traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1
  RowsValid (rs.map decodeRow) (Whole.initialRegisters hs hc) ∧
  (eval VerifierCommands.headerCommand (Whole.cleanRegisters e)).1=true ∧
  (eval VerifierCommands.rankCommand (Whole.cleanRegisters e)).1=true ∧
  (eval VerifierCommands.revenueCommand (eval VerifierCommands.rankCommand (Whole.cleanRegisters e)).2).1=true ∧
  ∃ t,Balance.loopValue (finalRegisters e) ((rs.map decodeRecord).reverse.map Balance.witnessTriple)=some t

lemma header_count_congr (s : Source) (q a b : ZBits) (h : zvalue a=zvalue b) :
    headerGuard s q a=headerGuard s q b := by
  unfold headerGuard positive
  rw [zle_value_congr (unsigned s.declaredCount) a (unsigned s.declaredCount) b rfl h,
    zle_value_congr a (unsigned s.declaredCount) b (unsigned s.declaredCount) h rfl,
    zle_value_congr a zzero b zzero h rfl,
    zle_value_congr (unsigned s.capacity) a (unsigned s.capacity) b rfl h]

lemma header_count_end (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) :
    (eval VerifierCommands.headerCommand (Whole.cleanRegisters
      (traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1)).1=
      headerGuard (parsedSource hs rs) (hc 0,hc 1) (countRecordBits (rs.map decodeRecord)) := by
  rw [header_check_end]
  apply header_count_congr
  have h := (trace_represents (rs.map decodeRow) (Whole.initialRegisters hs hc) [] streamInitial
    (initial_represents hs hc) rfl rfl).2
  simpa [Whole.initialRegisters,zzero_value,countRecordBits_value] using h

lemma rows_local_iff (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord)
    (hm : ∀ r∈rs,NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active) :
    RowsValid (rs.map decodeRow) (Whole.initialRegisters hs hc) ↔
      (rs.map decodeRecord).all recordLegal=true ∧ (rs.map decodeRecord).all (checkBasic (hc 0,hc 1))=true := by
  constructor
  · intro h
    have hh := RowsValid_local (rs.map decodeRow) (Whole.initialRegisters hs hc) h rfl
    constructor <;> apply List.all_eq_true.mpr <;> intro x hx <;>
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    · exact (hh (decodeRow r) (List.mem_map.mpr ⟨r,hr,rfl⟩)).1
    · exact (hh (decodeRow r) (List.mem_map.mpr ⟨r,hr,rfl⟩)).2
  · rintro ⟨hl,hb⟩
    apply RowsValid_of_local _ _ rfl
    · intro r hr
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      exact hm x hx
    · intro r hr
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      exact ⟨List.all_eq_true.mp hl _ (List.mem_map.mpr ⟨x,hx,rfl⟩),
        List.all_eq_true.mp hb _ (List.mem_map.mpr ⟨x,hx,rfl⟩)⟩

theorem semanticConditions_iff (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord)
    (hm : ∀ r∈rs,NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active) :
    semanticConditions hs hc rs ↔ (verifyParsed (parsedSource hs rs) (parsedCertificate hc rs)).1=true := by
  rw [←streamingVerifyParsed_eq]
  have hshape : shapeGuard (parsedSource hs rs) (parsedCertificate hc rs)=true :=
    shapeGuard_correct _ _ |>.mpr (by simp [ShapeValid,parsedSource,parsedCertificate])
  simp only [streamingVerifyParsed,hshape,if_true,parsed_sourceRecords,streamCheck,Bool.and_eq_true]
  unfold semanticConditions
  dsimp only
  have hbal:=balance_checks_end hs hc rs
  dsimp only at hbal
  rw [rows_local_iff hs hc rs hm,header_count_end,hbal]
  have hf := congrArg (fun b=>b=true) (final_checks_end hs hc rs)
  simp only [Bool.and_eq_true] at hf
  dsimp only [parsedSource,parsedCertificate] at hf ⊢
  rw [←hf]
  tauto

end BalancedAssortments.NPStack.SourceVerifier
