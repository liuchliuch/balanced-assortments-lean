import BalancedAssortments.NPCNFStackChainCost

namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate NPStackFields Encoding

theorem chain_halted_correct (initialSign : Bool) (next : List Bool) (a : BitLiteral) (rest : BitClause)
    (suffix out allocated : List Bool) {t : ℕ} {c : Config Register (Label State)} {accepted : Bool}
    (hr : Run (program initialSign) t
      (cfg (.readSign a.positive) (store (dataFields (clauseFields rest)++suffix) a.labelBits [] next out allocated)) c)
    (hc : (program initialSign).code c.pc=.halt accepted) :
    t=chainCost next a rest out ∧
      c=cfg .accept (store suffix (chainLast next a rest) [] (bitChain next a rest).1.2
        (out++bodyData (bitChain next a rest).1.1) (chainAllocated next rest++allocated)) := by
  exact hr.halted_unique (noChoice_deterministic (compile_noChoice macroCode (.readSign initialSign) .input .output))
    (chain_run initialSign next a rest suffix out allocated) hc rfl

end BalancedAssortments.NPCNF.StackChain
