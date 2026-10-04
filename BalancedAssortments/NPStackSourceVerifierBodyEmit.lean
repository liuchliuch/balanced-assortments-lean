import BalancedAssortments.NPStackSourceVerifierBodyCalls

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def emittedRowStore (active : Bool) (s : BodyStack→List Bool) : BodyStack→List Bool :=
  emittedStore .mask (Function.update (emittedStore .positive (emittedStore .negative s))
    (.inr (.inr .maskPayload)) [active])

lemma emit_row_run (active : Bool) (s : BodyStack→List Bool)
    (hs : s (.inr (.inr .emitScratch))=[])
    (hm : s (.inr (.inr .maskPayload))=[]) :
    Run innerProgram (5*((s (.inl 7)).length+(s (.inl 8)).length)+18)
      ⟨.emit active .negative .reverse,s⟩ ⟨.done,emittedRowStore active s⟩ := by
  let s1 := emittedStore .negative s
  let s2 := emittedStore .positive s1
  let s3 := Function.update s2 (.inr (.inr .maskPayload)) [active]
  have h1 := emit_run active .negative s hs
  have hs1 : s1 (.inr (.inr .emitScratch))=[] := by simp [s1,emittedStore,emitSource,Function.update,hs]
  have h2 := emit_run active .positive s1 hs1
  have hp : Step innerProgram ⟨.pushMask active,s2⟩ ⟨.emit active .mask .reverse,s3⟩ := by
    simp [Step,successors,innerProgram,s3,s2,s1,emittedStore,emitSource,Function.update,hm]
  have hs3 : s3 (.inr (.inr .emitScratch))=[] := by
    simp [s3,s2,s1,emittedStore,emitSource,Function.update,hs]
  have h3 := emit_run active .mask s3 hs3
  have h := ((h1.trans h2).trans (Run.one hp)).trans h3
  convert h using 1 <;> simp [s3,s2,s1,emittedRowStore,emitSource,emitNext,emittedStore,Function.update] <;> omega

lemma emitted_row_workspace (active : Bool) (s : Registers) (balance : List Bool) :
    ClearRows.cleared ClearRows.rowKeys (emittedRowStore active (packedStore s [] balance))=
      NPStackSourcePairing.rowStore (fun _=>[])
        (workspaceStore s (NPStackFields.dataFields [[active],(s .numerator).1,(s .numerator).2]++balance)) := by
  funext k
  cases k with
  | inl i => simp [ClearRows.cleared_apply,ClearRows.rowKeys,NPStackSourcePairing.rowStore]
  | inr w =>
    simp only [ClearRows.cleared_apply,ClearRows.rowKeys,List.mem_map,Sum.inl.injEq]
    simp only [not_false_eq_true,ite_false,NPStackSourcePairing.rowStore]
    cases w with
    | inr e => cases e <;>
        simp [emittedRowStore,emittedStore,emitSource,workspaceStore,packedStore,arithmeticInverse,
          extraStore,arithmeticMap,SignedAssignment.initialStore,SignedAssignment.store,Function.update,NPStackFields.dataFields,NPStackFields.tagBits,List.append_assoc]
    | inl a =>
      simp only [emittedRowStore,emittedStore,emitSource,Function.update]
      simp [workspaceStore,packedStore,extraStore]

end BalancedAssortments.NPStack.SourceVerifier
