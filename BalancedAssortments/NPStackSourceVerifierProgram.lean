import BalancedAssortments.NPStackSourceVerifierTraceSound
import BalancedAssortments.NPStackSourceVerifierHeaderCorrect
import BalancedAssortments.NPStackVerifierFinalSemantics
import BalancedAssortments.NPStackHandoff

namespace BalancedAssortments.NPStack.SourceVerifier.Whole
open NPStack DirectVerifier VerifierControl

abbrev RowControl := InnerState ⊕ ClearRows.ClearState (ClearRows.rowKeys (W:=Workspace))
abbrev PairControl := NPStackSourcePairing.State RowControl
abbrev HeaderGuard := VerifierControl.State VerifierCommands.Control VerifierCommands.headerCommand
abbrev RankGuard := VerifierControl.State VerifierCommands.Control VerifierCommands.rankCommand
abbrev RevenueGuard := VerifierControl.State VerifierCommands.Control VerifierCommands.revenueCommand

inductive State (Q : Type) | header (q : Header.State) | rows (q : PairControl) |
  headerGuard (q : HeaderGuard) | rankGuard (q : RankGuard) | revenueGuard (q : RevenueGuard) | balance (q : Q)
  deriving Fintype

def rowsProgram := NPStackSourcePairing.program SourceVerifier.bodyProgram
def headerGuardProgram := VerifierCommands.program VerifierCommands.headerCommand
def rankGuardProgram := VerifierCommands.program VerifierCommands.rankCommand
def revenueGuardProgram := VerifierCommands.program VerifierCommands.revenueCommand

def globalArithmeticMap (k : VerifierControl.Stack) : SourceVerifier.Stack := .body (arithmeticMap k)
lemma globalArithmeticMap_injective : Function.Injective globalArithmeticMap := by
  intro a b h
  exact arithmeticMap_injective (NPStackSourcePairing.Stack.body.inj h)

/-- The supplied balance loop is literal finite bytecode. Every earlier phase
is fixed concrete code; successful halts are replaced by one counted jump. -/
def program {Q : Type} (balanceProgram : Program BodyStack Q) : Program SourceVerifier.Stack (State Q) where
  start := .header Header.program.start
  inputStack := .source
  outputStack := .body balanceProgram.outputStack
  code
    | .header q => Handoff.code id State.header (.rows rowsProgram.start) (Header.program.code q)
    | .rows q => Handoff.code id State.rows (.headerGuard headerGuardProgram.start) (rowsProgram.code q)
    | .headerGuard q => Handoff.code globalArithmeticMap State.headerGuard (.rankGuard rankGuardProgram.start) (headerGuardProgram.code q)
    | .rankGuard q => Handoff.code globalArithmeticMap State.rankGuard (.revenueGuard revenueGuardProgram.start) (rankGuardProgram.code q)
    | .revenueGuard q => Handoff.code globalArithmeticMap State.revenueGuard (.balance balanceProgram.start) (revenueGuardProgram.code q)
    | .balance q => (balanceProgram.code q).rename NPStackSourcePairing.Stack.body State.balance

/-- A stage relation records an actual accepting finite subprogram execution,
its exact time, its projected registers, and every untouched caller register. -/
def StageRun {K Q : Type*} [DecidableEq K] (P : Program K Q) (fk : K→SourceVerifier.Stack)
    (before after : SourceVerifier.Stack→List Bool) (t : ℕ) : Prop :=
  ∃ e,Run P t ⟨P.start,fun k=>before (fk k)⟩ e ∧ accepts P e ∧
    (∀ k,after (fk k)=e.stk k) ∧ (∀ k,(∀ old,fk old≠k) → after k=before k)

/-- Exact composition of the six literal phases. The five successful handoffs
are real extra transitions, and no stage is an abstract verifier callback. -/
def Execution {Q : Type} (B : Program BodyStack Q) (before after : SourceVerifier.Stack→List Bool) (T : ℕ) : Prop :=
  ∃ h r g₁ g₂ g₃ th tr t₁ t₂ t₃ tb,
    StageRun Header.program id before h th ∧ StageRun rowsProgram id h r tr ∧
    StageRun headerGuardProgram globalArithmeticMap r g₁ t₁ ∧
    StageRun rankGuardProgram globalArithmeticMap g₁ g₂ t₂ ∧
    StageRun revenueGuardProgram globalArithmeticMap g₂ g₃ t₃ ∧
    StageRun B NPStackSourcePairing.Stack.body g₃ after tb ∧ T=th+tr+t₁+t₂+t₃+tb+5

lemma stage_mk {K Q : Type*} [DecidableEq K] (P : Program K Q) (fk : K→SourceVerifier.Stack)
    (before after : SourceVerifier.Stack→List Bool) {t : ℕ} {s : K→List Bool} {e : Config K Q}
    (hr : Run P t ⟨P.start,s⟩ e) (ha : accepts P e) (hb : ∀ k,before (fk k)=s k)
    (he : ∀ k,after (fk k)=e.stk k) (hf : ∀ k,(∀ old,fk old≠k) → after k=before k) :
    StageRun P fk before after t := by
  refine ⟨e,?_,ha,he,hf⟩
  have hs : (fun k=>before (fk k))=s := funext hb
  rw [hs]
  exact hr

lemma handoff_complete {K A R : Type*} [DecidableEq K]
    (P : Program K A) (target : Program SourceVerifier.Stack R) (fk : K→SourceVerifier.Stack) (fq : A→R) (next : R)
    (hinj : Function.Injective fk) (hcode : ∀ q,target.code (fq q)=Handoff.code fk fq next (P.code q))
    {before after : SourceVerifier.Stack→List Bool} {t : ℕ} (h : StageRun P fk before after t) :
    Run target (t+1) ⟨fq P.start,before⟩ ⟨next,after⟩ := by
  obtain ⟨e,hr,ha,he,hf⟩ := h
  exact Handoff.run fk fq next hinj hcode (before:=⟨fq P.start,before⟩) (after:=⟨fq e.pc,after⟩) hr ha ⟨rfl,fun _=>rfl⟩ ⟨rfl,he⟩ hf

lemma handoff_sound {K A R : Type*} [DecidableEq K]
    (P : Program K A) (target : Program SourceVerifier.Stack R) (fk : K→SourceVerifier.Stack) (fq : A→R) (next : R)
    (hinj : Function.Injective fk) (hcode : ∀ q,target.code (fq q)=Handoff.code fk fq next (P.code q))
    {before : SourceVerifier.Stack→List Bool} {T : ℕ} {out : Config SourceVerifier.Stack R}
    (hr : Run target T ⟨fq P.start,before⟩ out) (ha : accepts target out) :
    ∃ t u after,StageRun P fk before after t ∧ Run target u ⟨next,after⟩ out ∧ t+1+u=T := by
  obtain ⟨t,u,e,after,he,haccept,hrel,hframe,hrest,ht⟩ := Handoff.accepting_segment fk fq next hinj hcode
    (c:=⟨P.start,fun k=>before (fk k)⟩) ⟨rfl,fun _=>rfl⟩ hr ha
  exact ⟨t,u,after.stk,⟨e,he,haccept,hrel.2,hframe⟩,hrest,ht⟩

/-- Recover all concrete stage runs from any accepting complete verifier run. -/
theorem accepting_execution {Q : Type} (B : Program BodyStack Q) {before : SourceVerifier.Stack→List Bool}
    {T : ℕ} {out : Config SourceVerifier.Stack (State Q)}
    (hr : Run (program B) T ⟨(program B).start,before⟩ out) (ha : accepts (program B) out) :
    Execution B before out.stk T := by
  obtain ⟨th,u₀,h,hh,hr₀,ht₀⟩ := handoff_sound Header.program (program B) id State.header
    (.rows rowsProgram.start) Function.injective_id (fun _=>rfl) hr ha
  obtain ⟨tr,u₁,r,hrstage,hr₁,ht₁⟩ := handoff_sound rowsProgram (program B) id State.rows
    (.headerGuard headerGuardProgram.start) Function.injective_id (fun _=>rfl) hr₀ ha
  obtain ⟨t₁,u₂,g₁,hg₁,hr₂,ht₂⟩ := handoff_sound headerGuardProgram (program B) globalArithmeticMap State.headerGuard
    (.rankGuard rankGuardProgram.start) globalArithmeticMap_injective (fun _=>rfl) hr₁ ha
  obtain ⟨t₂,u₃,g₂,hg₂,hr₃,ht₃⟩ := handoff_sound rankGuardProgram (program B) globalArithmeticMap State.rankGuard
    (.revenueGuard revenueGuardProgram.start) globalArithmeticMap_injective (fun _=>rfl) hr₂ ha
  obtain ⟨t₃,tb,g₃,hg₃,hr₄,ht₄⟩ := handoff_sound revenueGuardProgram (program B) globalArithmeticMap State.revenueGuard
    (.balance B.start) globalArithmeticMap_injective (fun _=>rfl) hr₃ ha
  obtain ⟨e,he,hrel,hframe⟩ := hr₄.reflect NPStackSourcePairing.Stack.body State.balance
    (by intro a b h;cases h;rfl) (fun _=>rfl)
    (c:=⟨B.start,fun k=>g₃ (.body k)⟩) ⟨rfl,fun _=>rfl⟩
  have heaccept : accepts B e := accepts_reflect NPStackSourcePairing.Stack.body State.balance (fun _=>rfl) hrel ha
  refine ⟨h,r,g₁,g₂,g₃,th,tr,t₁,t₂,t₃,tb,hh,hrstage,hg₁,hg₂,hg₃,⟨e,he,heaccept,hrel.2,hframe⟩,?_⟩
  omega

/-- Conversely the actual component runs compose into an accepting execution
of the literal whole program, with the exact stored values and time. -/
theorem execution_complete {Q : Type} (B : Program BodyStack Q)
    {before after : SourceVerifier.Stack→List Bool} {T : ℕ} (h : Execution B before after T) :
    ∃ out,Run (program B) T ⟨(program B).start,before⟩ out ∧ accepts (program B) out ∧ out.stk=after := by
  obtain ⟨h,r,g₁,g₂,g₃,th,tr,t₁,t₂,t₃,tb,hh,hr,hg₁,hg₂,hg₃,hb,ht⟩ := h
  have hhead := handoff_complete Header.program (program B) id State.header (.rows rowsProgram.start)
    Function.injective_id (fun _=>rfl) hh
  have hrows := handoff_complete rowsProgram (program B) id State.rows (.headerGuard headerGuardProgram.start)
    Function.injective_id (fun _=>rfl) hr
  have hg1 := handoff_complete headerGuardProgram (program B) globalArithmeticMap State.headerGuard (.rankGuard rankGuardProgram.start)
    globalArithmeticMap_injective (fun _=>rfl) hg₁
  have hg2 := handoff_complete rankGuardProgram (program B) globalArithmeticMap State.rankGuard (.revenueGuard revenueGuardProgram.start)
    globalArithmeticMap_injective (fun _=>rfl) hg₂
  have hg3 := handoff_complete revenueGuardProgram (program B) globalArithmeticMap State.revenueGuard (.balance B.start)
    globalArithmeticMap_injective (fun _=>rfl) hg₃
  obtain ⟨e,he,ha,hproj,hframe⟩ := hb
  have hbal := he.relocate_exact (R:=program B) NPStackSourcePairing.Stack.body State.balance
    (by intro a b h;cases h;rfl) (fun _ _=>rfl)
    (c':=⟨.balance B.start,g₃⟩) (d':=⟨.balance e.pc,after⟩) ⟨rfl,fun _=>rfl⟩ ⟨rfl,hproj⟩ hframe
  have hall := hhead.trans (hrows.trans (hg1.trans (hg2.trans (hg3.trans hbal))))
  refine ⟨⟨.balance e.pc,after⟩,?_,?_,rfl⟩
  · convert hall using 1 <;> omega
  · change (B.code e.pc).rename NPStackSourcePairing.Stack.body State.balance=.halt true
    rw [ha]
    rfl

end BalancedAssortments.NPStack.SourceVerifier.Whole
