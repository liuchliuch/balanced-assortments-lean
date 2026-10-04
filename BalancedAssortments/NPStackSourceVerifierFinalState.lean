import BalancedAssortments.NPStackSourceVerifierProgramStore
import BalancedAssortments.NPStackSourceBalanceSemantics
import BalancedAssortments.NPStackSourceVerifierGrammar

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

lemma header_effect (s : Registers) : (eval VerifierCommands.headerCommand s).2=s := by
  simp only [VerifierCommands.headerCommand,VerifierCommands.guardLE,VerifierCommands.guardPositive,eval]
  split_ifs <;> rfl

def finalRegisters (s : Registers) : Registers :=
  (eval VerifierCommands.revenueCommand (eval VerifierCommands.rankCommand (Whole.cleanRegisters s)).2).2

lemma final_readonly (s : Registers) (k : RowReg)
    (hk : k∈[RowReg.q,.alpha,.alphaDen,.target,.targetDen,.capacity,.declaredCount,
      .rankDen,.rankNum,.revenueDen,.revenueNum,.total,.maximum,.count,.zero,.one]) :
    finalRegisters s k=s k := by
  have ht : k≠.term := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hp : k≠.product := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  unfold finalRegisters
  rw [(VerifierCommands.final_preserves _ k ht hp).2,(VerifierCommands.final_preserves _ k ht hp).1]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

lemma final_represents (s : Registers) (a : StreamState) (h : Represents s a) : Represents (finalRegisters s) a := by
  rcases h with ⟨hr,hv,ht,hm⟩
  have hh : registerState (finalRegisters s)=registerState s := by
    simp only [registerState,final_readonly s .rankDen (by simp),final_readonly s .rankNum (by simp),
      final_readonly s .revenueDen (by simp),final_readonly s .revenueNum (by simp),
      final_readonly s .total (by simp),final_readonly s .maximum (by simp)]
  simp only [Represents,hh,final_readonly s .maximum (by simp)]
  exact ⟨hr,hv,ht,hm⟩

lemma initial_represents (hs : Fin 8→List Bool) (hc : Fin 2→List Bool) :
    Represents (Whole.initialRegisters hs hc) streamInitial := by
  exact ⟨rfl,rfl,rfl,rfl⟩

lemma header_check_end (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) :
    (eval VerifierCommands.headerCommand (Whole.cleanRegisters
      (traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1)).1=
      headerGuard (parsedSource hs rs) (hc 0,hc 1)
        ((traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1 .count) := by
  rw [VerifierCommands.headerCommand_accepts _ (by
    change (traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1 .zero=zzero
    rw [trace_readonly _ _ _ .zero (by simp)];rfl)]
  simp only [Whole.cleanRegisters,loadRecord]
  simp only [trace_readonly _ _ _ .declaredCount (by simp),trace_readonly _ _ _ .capacity (by simp),
    trace_readonly _ _ _ .alpha (by simp),trace_readonly _ _ _ .alphaDen (by simp),
    trace_readonly _ _ _ .targetDen (by simp),trace_readonly _ _ _ .q (by simp)]
  rfl

lemma sequential_final_checks (s : Registers) :
    ((eval VerifierCommands.rankCommand (Whole.cleanRegisters s)).1 &&
      (eval VerifierCommands.revenueCommand (eval VerifierCommands.rankCommand (Whole.cleanRegisters s)).2).1)=
    ((eval VerifierCommands.rankCommand s).1 && (eval VerifierCommands.revenueCommand s).1) := by
  simp only [VerifierCommands.rankCommand_accepts,VerifierCommands.revenueCommand_accepts]
  rw [(VerifierCommands.final_preserves _ .target (by decide) (by decide)).1,
      (VerifierCommands.final_preserves _ .revenueDen (by decide) (by decide)).1,
      (VerifierCommands.final_preserves _ .q (by decide) (by decide)).1,
      (VerifierCommands.final_preserves _ .total (by decide) (by decide)).1,
      (VerifierCommands.final_preserves _ .targetDen (by decide) (by decide)).1,
      (VerifierCommands.final_preserves _ .revenueNum (by decide) (by decide)).1]
  rfl

lemma final_checks_end (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) :
    let e := (traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1
    ((eval VerifierCommands.rankCommand (Whole.cleanRegisters e)).1 &&
      (eval VerifierCommands.revenueCommand (eval VerifierCommands.rankCommand (Whole.cleanRegisters e)).2).1)=
      checkFinal (parsedSource hs rs).alpha (parsedSource hs rs).target (hs 1) (hc 0,hc 1)
        (streamFold (rs.map decodeRecord) streamInitial) := by
  dsimp only
  rw [sequential_final_checks]
  have hrep := (trace_represents (rs.map decodeRow) (Whole.initialRegisters hs hc) [] streamInitial
    (initial_represents hs hc) rfl rfl).1
  have he : (rs.map decodeRow).map Prod.fst=rs.map decodeRecord := by simp [List.map_map,Function.comp_def,decodeRow]
  rw [he] at hrep
  have hh := final_check_represented _ _ hrep (parsedSource hs rs).target (hs 1)
    (by rw [trace_readonly _ _ _ .capacity (by simp)];rfl)
    (by rw [trace_readonly _ _ _ .target (by simp)];rfl)
    (by rw [trace_readonly _ _ _ .targetDen (by simp)];rfl)
  rw [trace_readonly _ _ _ .q (by simp)] at hh
  exact hh

lemma balance_checks_end (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) :
    let e := (traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1
    (∃ t,Balance.loopValue (finalRegisters e) ((rs.map decodeRecord).reverse.map Balance.witnessTriple)=some t) ↔
      (rs.map decodeRecord).all (checkBalance (hs 2,hs 3) (hs 4,[])
        (streamFold (rs.map decodeRecord) streamInitial).maximum)=true := by
  dsimp only
  rw [Balance.witness_loop_accepts,List.all_reverse]
  rw [final_readonly _ .alpha (by simp),final_readonly _ .alphaDen (by simp),final_readonly _ .maximum (by simp)]
  rw [trace_readonly _ _ _ .alpha (by simp),trace_readonly _ _ _ .alphaDen (by simp)]
  have hrep := (trace_represents (rs.map decodeRow) (Whole.initialRegisters hs hc) [] streamInitial
    (initial_represents hs hc) rfl rfl).1
  have he : (rs.map decodeRow).map Prod.fst=rs.map decodeRecord := by simp [List.map_map,Function.comp_def,decodeRow]
  rw [he] at hrep
  have hf : checkBalance (hs 2,hs 3) (hs 4,[]) ((traceEnd (rs.map decodeRow) (Whole.initialRegisters hs hc) []).1 .maximum)=
      checkBalance (hs 2,hs 3) (hs 4,[]) (streamFold (rs.map decodeRecord) streamInitial).maximum := by
    funext x
    exact balance_check_congr _ _ _ _ x hrep.2.2.2
  change _=true ↔ _=true
  dsimp only [Whole.initialRegisters]
  rw [hf]

end BalancedAssortments.NPStack.SourceVerifier
