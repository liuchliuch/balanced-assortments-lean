import BalancedAssortments.NPStackSourceVerifierBodySound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma rowEffect_readonly (s : Registers) (k : RowReg)
    (hk : k∈[RowReg.price,.priceDen,.attraction,.attractionDen,.numerator,.q,.alpha,.alphaDen,
      .target,.targetDen,.capacity,.declaredCount,.zero,.one]) :
    VerifierCommands.rowEffect s k=s k := by
  have hn : k≠.maximum := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  unfold VerifierCommands.rowEffect
  rw [VerifierCommands.maxCommand_preserves _ k hn,accumulatorAssignments_preserves _ k hk]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [evalAssignments,capAssignments,evalAssignment,Function.update]

def loadRecord (s : Registers) (x : WitnessRecord) : Registers :=
  fun k => match k with
  | .price => x.price.num | .priceDen => (x.price.den,[])
  | .attraction => x.attraction.num | .attractionDen => (x.attraction.den,[])
  | .numerator => x.numerator | _ => s k

lemma loadRecord_holds (s : Registers) (x : WitnessRecord) : HoldsRecord (loadRecord s x) x := by
  simp [HoldsRecord,loadRecord]

lemma loadRecord_workspace (s : Registers) (x : WitnessRecord) (balance : List Bool)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[]) :
    workspaceStore (loadRecord s x) balance=workspaceStore s balance := by
  funext w
  cases w with
  | inr e => cases e <;> rfl
  | inl a => cases a with
    | reg k b => cases k <;> cases b <;>
        simp [workspaceStore,packedStore,arithmeticInverse,arithmeticMap,extraStore,
          SignedAssignment.initialStore,SignedAssignment.store,loadRecord,hp,hv]
    | work k => rfl
    | copyScratch => rfl
    | transferScratch => rfl

lemma rowEffect_denominators (s : Registers) (x : WitnessRecord) :
    ((VerifierCommands.rowEffect (loadRecord s x)) .priceDen).2=[] ∧
      ((VerifierCommands.rowEffect (loadRecord s x)) .attractionDen).2=[] := by
  rw [rowEffect_readonly _ .priceDen (by simp),rowEffect_readonly _ .attractionDen (by simp)]
  exact ⟨rfl,rfl⟩

end BalancedAssortments.NPStack.SourceVerifier
