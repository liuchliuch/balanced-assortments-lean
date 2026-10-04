import BalancedAssortments.NPStackSourceBalanceBody

namespace BalancedAssortments.NPStack.SourceVerifier.Balance
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl NPStackFields
instance clearStateDecidableEq {K : Type} : (ks : List K) → DecidableEq (ClearRows.ClearState ks)
  | [] => inferInstanceAs (DecidableEq Unit)
  | _::ks => letI := clearStateDecidableEq ks; inferInstanceAs (DecidableEq (Unit ⊕ ClearRows.ClearState ks))

abbrev BodyState := InnerState ⊕ ClearRows.ClearState (ClearRows.rowKeys (W:=Workspace))
inductive LoopState | probe | restore (b : Bool) | read (q : NPStackSourceRecords.State 3)
  | body (q : BodyState) | accept deriving DecidableEq,Fintype

def readMap : NPStackSourceRecords.Stack 3 → BodyStack
  | .input => .inr (.inr .balance)
  | .scratch => .inr (.inr .emitScratch)
  | .field i => .inl ⟨6+i.val,by omega⟩

def loopProgram : Program BodyStack LoopState where
  start := .probe
  inputStack := .inr (.inr .balance)
  outputStack := .inr (.inr .balance)
  code
    | .probe => .pop (.inr (.inr .balance)) .accept (.restore false) (.restore true)
    | .restore b => .push (.inr (.inr .balance)) b (.read (NPStackSourceRecords.atIndex 3 0))
    | .read .accept => .jump (.body bodyProgram.start)
    | .read q => ((NPStackSourceRecords.program 3).code q).rename readMap LoopState.read
    | .body q => match bodyProgram.code q with
      | .halt true => .jump .probe
      | .halt false => .halt false
      | i => i.rename id LoopState.body
    | .accept => .halt true

lemma readMap_injective : Function.Injective readMap := by
  intro a b h;cases a <;> cases b <;> simp_all [readMap]
  rename_i i j
  congr 1;apply Fin.ext
  exact h
lemma read_extends : CodeExtends (NPStackSourceRecords.program 3) loopProgram readMap LoopState.read := by
  intro q h;cases q <;> simp_all [loopProgram,NPStackSourceRecords.program]
lemma body_loop_extends : CodeExtends bodyProgram loopProgram id LoopState.body := by
  intro q h;cases he : bodyProgram.code q <;> simp_all [loopProgram]
lemma loop_noChoice : NoChoice loopProgram := by
  intro q x y
  cases q with
  | probe | restore b | accept => simp [loopProgram]
  | read q => cases q with
    | accept => simp [loopProgram]
    | field i q => cases q <;> simp [loopProgram,NPStackSourceRecords.program,NPStackFieldData.readProgram,Instr.rename]
  | body q =>
    have hn := body_noChoice q
    cases he : bodyProgram.code q <;> simp_all [loopProgram,Instr.rename]
    rename_i b;cases b <;> simp

abbrev Triple := Fin 3 → List Bool

def loaded (s : Registers) (x : Triple) : Registers := fun k =>
  match k with
  | .price | .attraction => ([],[])
  | .priceDen => ([],(s .priceDen).2)
  | .attractionDen => ([],(s .attractionDen).2)
  | .numerator => (x 1,x 2)
  | _ => s k

def rowFields (x : Triple) : Fin 9 → List Bool := fun i =>
  if h : 6 ≤ i.val then x ⟨i.val-6,by omega⟩ else []
def stable (s : Registers) (stream : List Bool) : BodyStack → List Bool :=
  NPStackSourcePairing.rowStore (fun _=>[]) (workspaceStore s stream)

lemma loaded_workspace (s : Registers) (x : Triple) (stream : List Bool) :
    workspaceStore (loaded s x) stream=workspaceStore s stream := by
  funext w
  cases w with
  | inr k => cases k <;> rfl
  | inl k => cases k with
    | reg k b => cases k <;> cases b <;> rfl
    | work k | copyScratch | transferScratch => rfl

lemma loaded_packed (s : Registers) (x : Triple) (stream : List Bool) :
    packedStore (loaded s x) (x 0) stream=
      NPStackSourcePairing.rowStore (rowFields x) (workspaceStore s stream) := by
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [packedStore,arithmeticInverse,arithmeticMap,extraStore,loaded,rowFields,
      NPStackSourcePairing.rowStore,SignedAssignment.initialStore,SignedAssignment.store]
  | inr w =>
    change packedStore (loaded s x) (x 0) stream (.inr w)=workspaceStore s stream w
    rw [packed_other_mask _ _ _ _ (by simp)]
    exact congrFun (loaded_workspace s x stream) w

lemma stable_balance (s : Registers) (stream : List Bool) : stable s stream (.inr (.inr .balance))=stream := rfl
lemma stable_update (s : Registers) (old new : List Bool) :
    Function.update (stable s old) (.inr (.inr .balance)) new=stable s new := by
  funext k;cases k with
  | inl i => simp [stable,NPStackSourcePairing.rowStore]
  | inr w => cases w with
    | inl k => cases k with
      | reg k b => cases k <;> cases b <;> simp [stable,NPStackSourcePairing.rowStore,workspaceStore,packedStore,arithmeticInverse,arithmeticMap,extraStore,Function.update]
      | work k | copyScratch | transferScratch => simp [stable,NPStackSourcePairing.rowStore,workspaceStore,packedStore,arithmeticInverse,arithmeticMap,extraStore,Function.update]
    | inr k => cases k <;> simp [stable,NPStackSourcePairing.rowStore,workspaceStore,packedStore,arithmeticInverse,extraStore,Function.update]

lemma extract_triple (s : Registers) (x : Triple) (stream : List Bool) :
    Run loopProgram (NPStackSourceRecords.recordCost (List.ofFn x))
      ⟨.read (NPStackSourceRecords.atIndex 3 0),stable s (dataFields (List.ofFn x)++stream)⟩
      ⟨.read .accept,packedStore (loaded s x) (x 0) stream⟩ := by
  rw [loaded_packed]
  apply (NPStackSourceRecords.extract_record x stream).relocate_exact readMap LoopState.read readMap_injective read_extends
  · constructor;rfl;intro k;cases k with
    | input | scratch => rfl
    | field i => rfl
  · constructor;rfl;intro k;cases k with
    | input | scratch => rfl
    | field i => simp [readMap,NPStackSourceRecords.cfg,NPStackSourceRecords.store,NPStackSourcePairing.rowStore,rowFields]
  · intro k hk
    cases k with
    | inl i =>
      have hi : ¬6 ≤ i.val := by
        intro hi
        exact hk (.field ⟨i.val-6,by omega⟩) (by unfold readMap; apply congrArg Sum.inl; apply Fin.ext; dsimp; omega)
      simp [NPStackSourcePairing.rowStore,stable,rowFields,hi]
    | inr w =>
      have hn := hk .input
      simp only [readMap] at hn
      simp only [NPStackSourcePairing.rowStore,stable]
      change packedStore s [] stream (.inr w)=packedStore s [] (dataFields (List.ofFn x)++stream) (.inr w)
      unfold packedStore
      cases arithmeticInverse (.inr w) <;> simp [extraStore,Ne.symm hn]

lemma probe_triple (s : Registers) (x : Triple) (stream : List Bool) :
    Run loopProgram 2 ⟨.probe,stable s (dataFields (List.ofFn x)++stream)⟩
      ⟨.read (NPStackSourceRecords.atIndex 3 0),stable s (dataFields (List.ofFn x)++stream)⟩ := by
  have hn : dataFields (List.ofFn x)++stream≠[] := by
    simp [List.ofFn_succ,dataFields,tagBits]
  generalize he : dataFields (List.ofFn x)++stream=bs at *
  cases bs with
  | nil => exact (hn rfl).elim
  | cons b bs =>
    have h1 : Step loopProgram ⟨.probe,stable s (b::bs)⟩ ⟨.restore b,stable s bs⟩ := by
      cases b <;> simp [Step,successors,loopProgram,stable_balance,stable_update]
    have h2 : Step loopProgram ⟨.restore b,stable s bs⟩ ⟨.read (NPStackSourceRecords.atIndex 3 0),stable s (b::bs)⟩ := by
      simp [Step,successors,loopProgram,stable_balance,stable_update]
    exact Run.succ h1 (.one h2)

end BalancedAssortments.NPStack.SourceVerifier.Balance
