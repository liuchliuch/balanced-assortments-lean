import BalancedAssortments.NPStackSourceVerifierBodySound
import BalancedAssortments.NPStackVerifierFinalSemantics

namespace BalancedAssortments.NPStack.SourceVerifier.Balance
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

abbrev FalseGuard := VerifierControl.State VerifierCommands.Control (VerifierCommands.balanceCommand false)
abbrev TrueGuard := VerifierControl.State VerifierCommands.Control (VerifierCommands.balanceCommand true)
inductive InnerState | mask (q : NPStackMask.State) | choose | guardFalse (q : FalseGuard) |
  guardTrue (q : TrueGuard) | done | reject deriving DecidableEq,Fintype

def guardLabel : (active : Bool) → VerifierControl.State VerifierCommands.Control (VerifierCommands.balanceCommand active) → InnerState
  | false,q => .guardFalse q | true,q => .guardTrue q

def guardReturn {A : Type} (f : A→InnerState) (i : Instr VerifierControl.Stack A) : Instr BodyStack InnerState :=
  match i with
  | .halt true => .jump .done
  | .halt false => .halt false
  | instr => instr.rename arithmeticMap f

def innerProgram : Program BodyStack InnerState where
  start := .mask .head
  inputStack := .inl 6
  outputStack := .inr (.inr .balance)
  code
    | .mask .accept => .jump .choose
    | .mask .reject => .halt false
    | .mask q => (NPStackMask.program.code q).rename maskMap InnerState.mask
    | .choose => .pop (.inr (.inr .maskFlag)) .reject
        (.guardFalse (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.balanceCommand false)))
        (.guardTrue (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.balanceCommand true)))
    | .guardFalse q => guardReturn InnerState.guardFalse ((VerifierCommands.program (VerifierCommands.balanceCommand false)).code q)
    | .guardTrue q => guardReturn InnerState.guardTrue ((VerifierCommands.program (VerifierCommands.balanceCommand true)).code q)
    | .done => .halt true
    | .reject => .halt false

def bodyProgram := ClearRows.finishProgram innerProgram ClearRows.rowKeys

lemma mask_extends : CodeExtends NPStackMask.program innerProgram maskMap InnerState.mask := by
  intro q h;cases q <;> simp_all [innerProgram,NPStackMask.program]
lemma guard_extends (active : Bool) :
    CodeExtends (VerifierCommands.program (VerifierCommands.balanceCommand active)) innerProgram arithmeticMap (guardLabel active) := by
  cases active <;> intro q h <;> dsimp only [innerProgram,guardLabel,guardReturn]
  all_goals
    cases he : (VerifierCommands.program _).code q with
    | halt b => exact (h b he).elim
    | jump q => rfl
    | push k b q => rfl
    | pop k e f t => rfl
    | choice l r => rfl

lemma inner_noChoice : NoChoice innerProgram := by
  have hg {A : Type} (f : A→InnerState) (i : Instr VerifierControl.Stack A)
      (hi : ∀ a b,i≠.choice a b) (x y : InnerState) : guardReturn f i≠.choice x y := by
    cases i <;> simp_all [guardReturn,Instr.rename]
    rename_i b;cases b <;> simp
  intro q x y
  cases q with
  | mask q => cases q <;> simp [innerProgram,NPStackMask.program,Instr.rename]
  | choose => simp [innerProgram]
  | guardFalse q => exact hg InnerState.guardFalse _ (VerifierCommands.command_noChoice _ q) x y
  | guardTrue q => exact hg InnerState.guardTrue _ (VerifierCommands.command_noChoice _ q) x y
  | done | reject => simp [innerProgram]

lemma body_noChoice : NoChoice bodyProgram := ClearRows.finish_noChoice innerProgram ClearRows.rowKeys inner_noChoice

lemma mask_run (s : Registers) (bits balance : List Bool) (active : Bool)
    (h : NPStackMask.maskValue bits=some active) :
    Run innerProgram (bits.length+4) ⟨.mask .head,packedStore s bits balance⟩
      ⟨guardLabel active (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.balanceCommand active)),
        packedStore s [] balance⟩ := by
  let mid := Function.update (packedStore s [] balance) (.inr (.inr .maskFlag)) [active]
  have hm : Run innerProgram (bits.length+2) ⟨.mask .head,packedStore s bits balance⟩ ⟨.mask .accept,mid⟩ := by
    apply (NPStackMask.mask_run bits [] active h).relocate_exact maskMap InnerState.mask maskMap_injective mask_extends
    · constructor; rfl; intro b;cases b <;> simp [maskMap,NPStackMask.cfg,NPStackMask.store]
    · constructor; rfl; intro b;cases b <;> simp [mid,maskMap,NPStackMask.cfg,NPStackMask.store,Function.update]
    · intro k hk
      have hm:=hk false;have hf:=hk true
      dsimp only [maskMap] at hm hf
      simpa [mid,Function.update,Ne.symm hf] using (packed_other_mask s bits balance k (Ne.symm hm)).symm
  have hj : Step innerProgram ⟨.mask .accept,mid⟩ ⟨.choose,mid⟩ := by simp [Step,successors,innerProgram]
  have he : Function.update mid (.inr (.inr .maskFlag)) []=packedStore s [] balance := by
    funext k
    by_cases hk : k=.inr (.inr .maskFlag)
    · subst k;simp [mid]
    · simp [mid,Function.update,hk]
  have hp : Step innerProgram ⟨.choose,mid⟩
      ⟨guardLabel active (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.balanceCommand active)),
        packedStore s [] balance⟩ := by
    cases active <;> simp [Step,successors,innerProgram,mid,Function.update_idem,he,guardLabel]
  convert (hm.trans (Run.one hj)).trans (Run.one hp) using 1 <;> omega

lemma guard_run (s : Registers) (balance : List Bool) (active : Bool) :
    ∃ t≤VerifierControl.budget VerifierCommands.compareTime (VerifierCommands.balanceCommand active) s,
      Run innerProgram t
        ⟨guardLabel active (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.balanceCommand active)),packedStore s [] balance⟩
        ⟨guardLabel active (VerifierControl.terminal (VerifierCommands.balanceCommand active) s),
          packedStore (VerifierControl.eval (VerifierCommands.balanceCommand active) s).2 [] balance⟩ := by
  obtain ⟨t,ht,hr⟩ := VerifierCommands.command_run (VerifierCommands.balanceCommand active) s
  refine ⟨t,ht,hr.relocate_exact arithmeticMap (guardLabel active) arithmeticMap_injective (guard_extends active) ?_ ?_ ?_⟩
  · exact ⟨rfl,packed_projection s [] balance⟩
  · exact ⟨rfl,packed_projection _ [] balance⟩
  · intro k hk
    exact (packed_frame s _ [] balance k hk).symm

lemma guard_exit (s : Registers) (active : Bool) :
    innerProgram.code (guardLabel active (VerifierControl.terminal (VerifierCommands.balanceCommand active) s))=
      if (VerifierControl.eval (VerifierCommands.balanceCommand active) s).1 then
        .jump .done else .halt false := by
  have hh := VerifierControl.terminal_halts VerifierCommands.comparisons SignedAssignCompare.State.result
    (VerifierCommands.balanceCommand active) s
  cases active
  · rfl
  · change guardReturn _ _=_
    
    unfold guardReturn
    change (VerifierCommands.program _).code _ = _ at hh
    rw [hh]
    cases he : (VerifierControl.eval (VerifierCommands.balanceCommand _) s).1 <;> rfl

def effect (active : Bool) (s : Registers) : Registers := (eval (VerifierCommands.balanceCommand active) s).2

lemma inner_row_run (s : Registers) (mask stream : List Bool) (active : Bool)
    (hm : NPStackMask.maskValue mask=some active) (ha : (eval (VerifierCommands.balanceCommand active) s).1=true) :
    ∃ t ≤ mask.length+5+VerifierControl.budget VerifierCommands.compareTime (VerifierCommands.balanceCommand active) s,
      Run innerProgram t ⟨.mask .head,packedStore s mask stream⟩ ⟨.done,packedStore (effect active s) [] stream⟩ := by
  obtain ⟨t,ht,hr⟩ := guard_run s stream active
  have hj : Step innerProgram
      ⟨guardLabel active (terminal (VerifierCommands.balanceCommand active) s),packedStore (effect active s) [] stream⟩
      ⟨.done,packedStore (effect active s) [] stream⟩ := by
    simp [Step,successors,guard_exit,ha]
  exact ⟨_,by omega,(mask_run s mask stream active hm).trans (hr.trans (.one hj))⟩

lemma cleared_workspace (s : Registers) (stream : List Bool) :
    ClearRows.cleared ClearRows.rowKeys (packedStore s [] stream)=
      NPStackSourcePairing.rowStore (fun _=>[]) (workspaceStore s stream) := by
  funext k;cases k with
  | inl i => simp [ClearRows.cleared_apply,ClearRows.rowKeys,NPStackSourcePairing.rowStore]
  | inr w => simp [ClearRows.cleared_apply,ClearRows.rowKeys,NPStackSourcePairing.rowStore,workspaceStore]

theorem body_row_run (s : Registers) (mask stream : List Bool) (active : Bool)
    (hm : NPStackMask.maskValue mask=some active) (ha : (eval (VerifierCommands.balanceCommand active) s).1=true) :
    ∃ t ≤ mask.length+6+VerifierControl.budget VerifierCommands.compareTime (VerifierCommands.balanceCommand active) s+
        ClearRows.clearCost ClearRows.rowKeys (packedStore (effect active s) [] stream),
      Run bodyProgram t ⟨bodyProgram.start,packedStore s mask stream⟩
        ⟨.inr (ClearRows.clearDone ClearRows.rowKeys),NPStackSourcePairing.rowStore (fun _=>[]) (workspaceStore (effect active s) stream)⟩ := by
  obtain ⟨t,ht,hr⟩ := inner_row_run s mask stream active hm ha
  have hh := ClearRows.finish_run innerProgram ClearRows.rowKeys hr (by rfl)
  rw [cleared_workspace] at hh
  refine ⟨_,?_,hh⟩
  change t + 1 + ClearRows.clearCost ClearRows.rowKeys (packedStore (effect active s) [] stream) ≤ _
  omega

lemma inner_bad_mask (s : Registers) (mask balance : List Bool)
    (hm : NPStackMask.maskValue mask=none) :
    ∃ t e,Run innerProgram t ⟨.mask .head,packedStore s mask balance⟩ e ∧ innerProgram.code e.pc=.halt false := by
  obtain ⟨t,ht,rest,hr⟩ := NPStackMask.mask_reject mask [] hm
  refine ⟨t,⟨.mask .reject,packedStore s rest balance⟩,?_,rfl⟩
  apply hr.relocate_exact maskMap InnerState.mask maskMap_injective mask_extends
  · constructor;rfl;intro b;cases b <;> simp [maskMap,NPStackMask.cfg,NPStackMask.store]
  · constructor;rfl;intro b;cases b <;> simp [maskMap,NPStackMask.cfg,NPStackMask.store]
  · intro k hk
    have h:=hk false
    dsimp only [maskMap] at h
    exact (packed_other_mask s rest balance k (Ne.symm h)).trans
      (packed_other_mask s mask balance k (Ne.symm h)).symm

lemma inner_bad_guard (s : Registers) (mask balance : List Bool) (active : Bool)
    (hm : NPStackMask.maskValue mask=some active)
    (ha : (eval (VerifierCommands.balanceCommand active) s).1=false) :
    ∃ t e,Run innerProgram t ⟨.mask .head,packedStore s mask balance⟩ e ∧ innerProgram.code e.pc=.halt false := by
  obtain ⟨t,ht,hr⟩ := guard_run s balance active
  refine ⟨_,_,(mask_run s mask balance active hm).trans hr,?_⟩
  simp [guard_exit,ha]


theorem inner_accepting_result (s : Registers) (mask stream : List Bool)
    {t : ℕ} {out : Config BodyStack InnerState}
    (hr : Run innerProgram t ⟨.mask .head,packedStore s mask stream⟩ out) (ha : accepts innerProgram out) :
    ∃ active,NPStackMask.maskValue mask=some active ∧
      (eval (VerifierCommands.balanceCommand active) s).1=true ∧ out=⟨.done,packedStore (effect active s) [] stream⟩ := by
  cases hm : NPStackMask.maskValue mask with
  | none =>
    obtain ⟨u,e,he,hh⟩ := inner_bad_mask s mask stream hm
    exact False.elim (rejecting_run_excludes_acceptance (noChoice_deterministic inner_noChoice) he hh hr ha)
  | some active =>
    cases hb : (eval (VerifierCommands.balanceCommand active) s).1 with
    | false =>
      obtain ⟨u,e,he,hh⟩ := inner_bad_guard s mask stream active hm hb
      exact False.elim (rejecting_run_excludes_acceptance (noChoice_deterministic inner_noChoice) he hh hr ha)
    | true =>
      obtain ⟨u,_,hu⟩ := inner_row_run s mask stream active hm hb
      have he := hr.halted_unique (noChoice_deterministic inner_noChoice) hu ha rfl
      exact ⟨active,rfl,hb,he.2⟩

theorem body_accepting_result (s : Registers) (mask stream : List Bool)
    {t : ℕ} {out : Config BodyStack (InnerState ⊕ ClearRows.ClearState ClearRows.rowKeys)}
    (hr : Run bodyProgram t ⟨bodyProgram.start,packedStore s mask stream⟩ out) (ha : accepts bodyProgram out) :
    ∃ active,NPStackMask.maskValue mask=some active ∧
      (eval (VerifierCommands.balanceCommand active) s).1=true ∧
      out.stk=NPStackSourcePairing.rowStore (fun _=>[]) (workspaceStore (effect active s) stream) := by
  obtain ⟨u,e,he,hh,hstore⟩ := ClearRows.finish_accepting_store innerProgram ClearRows.rowKeys
    ⟨.mask .head,packedStore s mask stream⟩ hr ha
  obtain ⟨active,hm,hb,heq⟩ := inner_accepting_result s mask stream he hh
  subst e
  rw [cleared_workspace] at hstore
  exact ⟨active,hm,hb,hstore⟩

end BalancedAssortments.NPStack.SourceVerifier.Balance
