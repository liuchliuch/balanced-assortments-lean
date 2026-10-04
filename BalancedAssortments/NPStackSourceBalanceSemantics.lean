import BalancedAssortments.NPStackSourceBalanceCorrect
import BalancedAssortments.NPStackSourceVerifierCheckSemantics

namespace BalancedAssortments.NPStack.SourceVerifier.Balance
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def witnessTriple (x : WitnessRecord) : Triple := ![[x.active],x.numerator.1,x.numerator.2]

lemma witnessTriple_fields (x : WitnessRecord) : List.ofFn (witnessTriple x)=witnessBalanceFields x := by
  simp [witnessTriple,witnessBalanceFields,List.ofFn_succ]

lemma witness_step (s : Registers) (x : WitnessRecord) :
    stepValue s (witnessTriple x)=
      if checkBalance (s .alpha) (s .alphaDen) (s .maximum) x then
        some (effect x.active (loaded s (witnessTriple x))) else none := by
  simp only [stepValue,witnessTriple,Matrix.cons_val_zero,NPStackMask.maskValue,List.all_nil,
    Bool.true_eq,Option.bind_some,VerifierCommands.balanceCommand_accepts]
  cases h : x.active <;> simp [h,loaded,witnessTriple,checkBalance]

lemma effect_keys (s : Registers) (x : WitnessRecord) (k : RowReg)
    (hk : k∈[RowReg.alpha,.alphaDen,.maximum]) :
    effect x.active (loaded s (witnessTriple x)) k=s k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl <;>
    rw [effect,VerifierCommands.balance_preserves _ _ _ (by decide) (by decide)] <;> rfl

lemma witness_loop_accepts (xs : List WitnessRecord) (s : Registers) :
    (∃ t,loopValue s (xs.map witnessTriple)=some t) ↔
      xs.all (checkBalance (s .alpha) (s .alphaDen) (s .maximum))=true := by
  induction xs generalizing s with
  | nil => simp [loopValue]
  | cons x xs ih =>
    simp only [List.map_cons,loopValue,witness_step,List.all_cons,Bool.and_eq_true]
    cases hb : checkBalance (s .alpha) (s .alphaDen) (s .maximum) x with
    | false => simp [hb]
    | true =>
      simp only [hb,if_true,Option.bind_some,true_and]
      rw [ih]
      simp only [effect_keys _ _ .alpha (by simp),effect_keys _ _ .alphaDen (by simp),effect_keys _ _ .maximum (by simp)]

lemma witness_stream (xs : List WitnessRecord) :
    stream (xs.map witnessTriple)=NPStackFields.dataFields (xs.flatMap witnessBalanceFields) := by
  simp [stream,List.flatMap_map,Function.comp_def,witnessTriple,witnessBalanceFields]
  rfl

end BalancedAssortments.NPStack.SourceVerifier.Balance
