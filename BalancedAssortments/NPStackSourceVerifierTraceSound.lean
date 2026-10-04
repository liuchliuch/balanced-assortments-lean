import BalancedAssortments.NPStackSourceVerifierTrace

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def decodeRecord (r : NPStackSourcePairing.PairRecord) : WitnessRecord where
  price := ⟨(r.1 0,r.1 1),r.1 2⟩
  attraction := ⟨(r.1 3,r.1 4),r.1 5⟩
  numerator := (r.2 1,r.2 2)
  active := (NPStackMask.maskValue (r.2 0)).getD false

def decodeRow (r : NPStackSourcePairing.PairRecord) : InputRow := (decodeRecord r,r.2 0)

lemma decodeRecord_pair (r : NPStackSourcePairing.PairRecord) :
    pairRecord (decodeRecord r) (r.2 0)=r := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

lemma raw_body_sound (r : NPStackSourcePairing.PairRecord) (s : Registers) (balance : List Bool)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[])
    {t : ℕ} {out : Config BodyStack (InnerState ⊕ ClearRows.ClearState ClearRows.rowKeys)}
    (hr : Run bodyProgram t ⟨bodyProgram.start,NPStackSourcePairing.rowStore
      (NPStackSourcePairing.pairedRow r.1 r.2) (workspaceStore s balance)⟩ out)
    (ha : accepts bodyProgram out) :
    NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active ∧
    (eval (VerifierCommands.rowCommand (decodeRecord r).active) (loadRecord s (decodeRecord r))).1=true ∧
    out.stk=NPStackSourcePairing.rowStore (fun _=>[])
      (workspaceStore (nextRegisters s (decodeRecord r)) (nextBalance s (decodeRecord r) balance)) := by
  have hs : packedStore (loadRecord s (decodeRecord r)) (r.2 0) balance=
      NPStackSourcePairing.rowStore (NPStackSourcePairing.pairedRow r.1 r.2) (workspaceStore s balance) := by
    rw [packed_record _ _ _ _ (loadRecord_holds _ _),loadRecord_workspace _ _ _ hp hv,
      ←pairRecord_fields,decodeRecord_pair]
  rw [←hs] at hr
  obtain ⟨active,hm,hb,hstore⟩ := body_accepting_result _ _ _ hr ha
  have he : (decodeRecord r).active=active := by simp [decodeRecord,hm]
  simpa only [he,nextRegisters,nextBalance] using And.intro hm (And.intro hb hstore)

theorem trace_sound {records : List NPStackSourcePairing.PairRecord}
    {work finish : Workspace→List Bool} {t : ℕ}
    (h : NPStackSourcePairing.BodyRuns bodyProgram records work finish t)
    (s : Registers) (balance : List Bool) (hw : work=workspaceStore s balance)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[]) :
    RowsValid (records.map decodeRow) s ∧
      finish=workspaceStore (traceEnd (records.map decodeRow) s balance).1
        (traceEnd (records.map decodeRow) s balance).2 := by
  induction h generalizing s balance with
  | nil work => exact ⟨trivial,hw⟩
  | @cons r rs work next finish t u q hr ha htail ih =>
    rw [hw] at hr
    obtain ⟨hm,hb,hstore⟩ := raw_body_sound r s balance hp hv hr ha
    have hn : next=workspaceStore (nextRegisters s (decodeRecord r)) (nextBalance s (decodeRecord r) balance) := by
      funext w
      exact congrFun hstore (.inr w)
    have hd := rowEffect_denominators s (decodeRecord r)
    obtain ⟨hvalid,hfinish⟩ := ih (nextRegisters s (decodeRecord r)) (nextBalance s (decodeRecord r) balance) hn hd.1 hd.2
    exact ⟨⟨hm,hb,hvalid⟩,hfinish⟩

end BalancedAssortments.NPStack.SourceVerifier
