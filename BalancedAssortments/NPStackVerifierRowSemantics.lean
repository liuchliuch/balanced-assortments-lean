import BalancedAssortments.NPStackVerifierCommands

namespace BalancedAssortments.NPStack.VerifierCommands
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma rowCommand_accepts (s : Registers) (x : WitnessRecord) (hx : HoldsRecord s x)
    (hz : s .zero=zzero) :
    (eval (rowCommand x.active) s).1=(recordLegal x && checkBasic (s .q) x) := by
  rcases hx with ⟨hr,hrd,hv,hvd,hp⟩
  cases h : x.active <;>
    simp only [rowCommand,h,Bool.false_eq_true,if_false,if_true,guardPositive_accepts,
      guardLE_accepts,eval_script,maxCommand_accepts,Bool.and_true]
  all_goals simp [evalAssignments,capAssignments,evalAssignment,Function.update,
    hr,hrd,hv,hvd,hp,hz,recordLegal,checkBasic,positive,unsigned,h,Bool.and_assoc]

def rowEffect (s : Registers) : Registers :=
  (eval maxCommand (evalAssignments accumulatorAssignments (evalAssignments capAssignments s))).2

lemma rowCommand_effect (active : Bool) (s : Registers)
    (h : (eval (rowCommand active) s).1=true) :
    (eval (rowCommand active) s).2=rowEffect s := by
  simp only [rowCommand,guardPositive,guardLE,eval] at h ⊢
  split_ifs at h <;> simp_all [rowEffect,eval]
  all_goals split_ifs at h <;> simp_all [rowEffect,eval]

lemma cap_preserves_record (s : Registers) (x : WitnessRecord) (hx : HoldsRecord s x) :
    HoldsRecord (evalAssignments capAssignments s) x := by
  rcases hx with ⟨hr,hrd,hv,hvd,hp⟩
  simp [HoldsRecord,evalAssignments,capAssignments,evalAssignment,Function.update,hr,hrd,hv,hvd,hp]
lemma cap_preserves_state (s : Registers) :
    registerState (evalAssignments capAssignments s)=registerState s := by
  simp [registerState,evalAssignments,capAssignments,evalAssignment,Function.update]

lemma maxCommand_preserves (s : Registers) (k : RowReg) (hk : k≠.maximum) :
    (eval maxCommand s).2 k=s k := by
  simp only [maxCommand,eval]
  split_ifs <;> simp [evalAssignments,evalAssignment,Function.update,hk]

lemma maxCommand_value (s : Registers) (hz : s .zero=zzero) :
    zvalue ((eval maxCommand s).2 .maximum)=max (zvalue (s .maximum)) (zvalue (s .numerator)) := by
  have hc := zle_correct (s .maximum) (s .numerator)
  simp only [maxCommand,eval]
  split_ifs with h
  · simp only [evalAssignments,List.foldl_cons,List.foldl_nil,evalAssignment,Function.update_self,
      zadd_value,hz,zzero_value,add_zero]
    exact (max_eq_right (hc.mp h)).symm
  · simp only
    exact (max_eq_left ((lt_of_not_ge (fun hh => h (hc.mpr hh))).le)).symm

/-- Correct decoded arithmetic effect of the literal row command, including
the maximum branch and the real record-count increment. -/
theorem rowEffect_spec (s : Registers) (x : WitnessRecord) (hx : HoldsRecord s x)
    (hz : s .zero=zzero) (hone : s .one=zOne) :
    (registerState (rowEffect s)).rank=(streamStep (registerState s) x).rank ∧
    (registerState (rowEffect s)).revenue=(streamStep (registerState s) x).revenue ∧
    (registerState (rowEffect s)).total=(streamStep (registerState s) x).total ∧
    zvalue ((rowEffect s) .maximum)=max (zvalue (s .maximum)) (zvalue x.numerator) ∧
    zvalue ((rowEffect s) .count)=zvalue (s .count)+1 := by
  let r := evalAssignments capAssignments s
  let u := evalAssignments accumulatorAssignments r
  have hr := cap_preserves_record s x hx
  have hspec := accumulatorAssignments_correct r x hr
  have hs := cap_preserves_state s
  have huz : u .zero=zzero := by
    dsimp only [u]
    rw [accumulatorAssignments_preserves r .zero (by simp)]
    simpa [r,evalAssignments,capAssignments,evalAssignment,Function.update] using hz
  have hun : u .numerator=x.numerator := by
    dsimp only [u]
    rw [accumulatorAssignments_preserves r .numerator (by simp)]
    exact hr.2.2.2.2
  have hum : u .maximum=s .maximum := hspec.2.2.2.2.trans (by simp [r,evalAssignments,capAssignments,evalAssignment,Function.update])
  have hmax := maxCommand_value u huz
  rw [hun,hum] at hmax
  have hc : zvalue (u .count)=zvalue (s .count)+1 := by
    dsimp only [u]
    rw [hspec.2.2.2.1,zadd_value]
    simp [r,evalAssignments,capAssignments,evalAssignment,Function.update,hone,add_comm]
  refine ⟨?_,?_,?_,hmax,?_⟩
  · change ((eval maxCommand u).2 .rankDen,(eval maxCommand u).2 .rankNum)=_
    rw [maxCommand_preserves u .rankDen (by decide),maxCommand_preserves u .rankNum (by decide)]
    simpa only [r,hs] using hspec.1
  · change ((eval maxCommand u).2 .revenueDen,(eval maxCommand u).2 .revenueNum)=_
    rw [maxCommand_preserves u .revenueDen (by decide),maxCommand_preserves u .revenueNum (by decide)]
    simpa only [r,hs] using hspec.2.1
  · change (eval maxCommand u).2 .total=_
    rw [maxCommand_preserves u .total (by decide)]
    simpa only [r,hs] using hspec.2.2.1
  · change zvalue ((eval maxCommand u).2 .count)=_
    rw [maxCommand_preserves u .count (by decide)]
    exact hc

/-- An accepting run of the actual finite row command cannot bypass a local
source-domain or witness-bound check. -/
theorem row_command_sound (s : Registers) (x : WitnessRecord) (hx : HoldsRecord s x)
    (hz : s .zero=zzero) {t : ℕ}
    {out : Config VerifierControl.Stack (VerifierControl.State Control (rowCommand x.active))}
    (hr : Run (program (rowCommand x.active)) t (cfg (rowCommand x.active) s) out)
    (ha : accepts (program (rowCommand x.active)) out) :
    recordLegal x=true ∧ checkBasic (s .q) x=true ∧
      out.stk=SignedAssignment.initialStore (rowEffect s) := by
  have hh := command_halted_result _ _ hr ha
  have hb := terminal_halts comparisons SignedAssignCompare.State.result (rowCommand x.active) s
  rw [hh.2] at ha
  change (program (rowCommand x.active)).code (terminal (rowCommand x.active) s)=.halt true at ha
  have hres : (eval (rowCommand x.active) s).1=true := Instr.halt.inj (hb.symm.trans ha)
  have hchecks := hres
  rw [rowCommand_accepts s x hx hz] at hchecks
  have he := rowCommand_effect x.active s hres
  have hchecks' : recordLegal x=true ∧ checkBasic (s .q) x=true := by simpa using hchecks
  refine ⟨hchecks'.1,hchecks'.2,?_⟩
  rw [hh.2]
  exact congrArg SignedAssignment.initialStore he

end BalancedAssortments.NPStack.VerifierCommands
