import BalancedAssortments.NPStackSourceVerifierProgram

set_option maxHeartbeats 2000000

namespace BalancedAssortments.NPStack.SourceVerifier.Whole
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

/-- Exact signed-register initialization from the ten literal raw header fields.
No canonicalization or positivity is assumed by this storage definition. -/
def initialRegisters (s : Fin 8→List Bool) (c : Fin 2→List Bool) : Registers
  | .declaredCount => (s 0,[])
  | .capacity => (s 1,[])
  | .alpha => (s 2,s 3)
  | .alphaDen => (s 4,[])
  | .target => (s 5,s 6)
  | .targetDen => (s 7,[])
  | .q => (c 0,c 1)
  | .rankDen | .revenueDen | .one => zOne
  | _ => zzero

/-- The physical header initializer agrees on every register, including unused
arithmetic shadow copies, with the first-pass pairing workspace convention. -/
theorem prepared_workspace (s : Fin 8→List Bool) (c : Fin 2→List Bool) :
    Header.preparedValues s c=NPStackSourcePairing.rowStore (fun _=>[])
      (workspaceStore (initialRegisters s c) []) := by
  funext k
  cases k with
  | inl i =>
    simp [Header.preparedValues,Header.headerValues,Header.sourceValues,sourceHeader,certificateHeader,
      Header.rankDen,Header.revenueDen,Header.one,NPStackSourcePairing.rowStore]
  | inr w =>
    cases w with
    | inr e => cases e <;>
        simp [Header.preparedValues,Header.headerValues,Header.sourceValues,sourceHeader,certificateHeader,
          Header.rankDen,Header.revenueDen,Header.one,NPStackSourcePairing.rowStore,workspaceStore,
          packedStore,arithmeticInverse,extraStore]
    | inl a => cases a with
      | reg r b => cases r <;> cases b <;>
          simp only [NPStackSourcePairing.rowStore,workspaceStore,packedStore,arithmeticInverse,arithmeticMap,
            SignedAssignment.initialStore,SignedAssignment.store,initialRegisters,zOne,zzero,extraStore]
          <;> first
          | exact Header.prepared_source s c 0
          | exact Header.prepared_source s c 1
          | exact Header.prepared_source s c 2
          | exact Header.prepared_source s c 3
          | exact Header.prepared_source s c 4
          | exact Header.prepared_source s c 5
          | exact Header.prepared_source s c 6
          | exact Header.prepared_source s c 7
          | exact Header.prepared_certificate s c 0
          | exact Header.prepared_certificate s c 1
          | exact Header.prepared_rankDen s c
          | exact Header.prepared_revenueDen s c
          | exact Header.prepared_one s c
          | apply Header.prepared_other <;> decide
      | work a =>
          simp [Header.preparedValues,Header.headerValues,Header.sourceValues,sourceHeader,certificateHeader,
            Header.rankDen,Header.revenueDen,Header.one,NPStackSourcePairing.rowStore,workspaceStore,
            packedStore,arithmeticInverse,arithmeticMap,extraStore,SignedAssignment.initialStore,SignedAssignment.store]
      | copyScratch | transferScratch =>
          simp [Header.preparedValues,Header.headerValues,Header.sourceValues,sourceHeader,certificateHeader,
            Header.rankDen,Header.revenueDen,Header.one,NPStackSourcePairing.rowStore,workspaceStore,
            packedStore,arithmeticInverse,arithmeticMap,extraStore,SignedAssignment.initialStore,SignedAssignment.store]

lemma prepared_global_store (s : Fin 8→List Bool) (c : Fin 2→List Bool) (sr cr : List Bool) :
    Header.store sr cr (Header.preparedValues s c)=
      (NPStackSourcePairing.cfg (Q:=RowControl) .probe sr cr [] (fun _=>[])
        (workspaceStore (initialRegisters s c) [])).stk := by
  rw [prepared_workspace]
  funext k;cases k <;> rfl

/-- Physical row registers are cleared after the first pass. Reloading an
empty record makes their logical values agree without changing any global
header or accumulator register. -/
def emptyRecord : WitnessRecord where
  price := ⟨zzero,[]⟩
  attraction := ⟨zzero,[]⟩
  numerator := zzero
  active := false

def cleanRegisters (s : Registers) : Registers := loadRecord s emptyRecord

lemma clean_workspace (s : Registers) (balance : List Bool)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[]) :
    workspaceStore (cleanRegisters s) balance=workspaceStore s balance :=
  loadRecord_workspace s emptyRecord balance hp hv

lemma packed_clean (s : Registers) (balance : List Bool)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[]) :
    packedStore (cleanRegisters s) [] balance=
      NPStackSourcePairing.rowStore (fun _=>[]) (workspaceStore s balance) := by
  have hh := packed_record (cleanRegisters s) emptyRecord [] balance (loadRecord_holds s emptyRecord)
  have hrow : recordFields emptyRecord []=(fun _=>[]) := by funext i;fin_cases i <;> rfl
  rw [hrow,clean_workspace s balance hp hv] at hh
  exact hh

def globalStore (s : Registers) (balance : List Bool) : SourceVerifier.Stack→List Bool :=
  Header.store [] [] (packedStore s [] balance)

lemma global_projection (s : Registers) (balance : List Bool) (k : VerifierControl.Stack) :
    globalStore s balance (globalArithmeticMap k)=SignedAssignment.initialStore s k :=
  packed_projection s [] balance k

lemma global_frame (s t : Registers) (balance : List Bool) (k : SourceVerifier.Stack)
    (hk : ∀ a,globalArithmeticMap a≠k) : globalStore s balance k=globalStore t balance k := by
  cases k with
  | source | certificate | scratch => rfl
  | body k =>
    exact packed_frame s t [] balance k (fun a h=>hk a (congrArg NPStackSourcePairing.Stack.body h))

lemma rows_to_globalStore (s : Registers) (balance : List Bool)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[]) :
    (NPStackSourcePairing.cfg (Q:=RowControl) .accept [] [] [] (fun _=>[]) (workspaceStore s balance)).stk=
      globalStore (cleanRegisters s) balance := by
  unfold globalStore
  rw [packed_clean s balance hp hv]
  funext k;cases k <;> rfl

end BalancedAssortments.NPStack.SourceVerifier.Whole
