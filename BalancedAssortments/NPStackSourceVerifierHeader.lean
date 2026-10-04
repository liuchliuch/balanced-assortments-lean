import BalancedAssortments.NPStackSourceVerifierLayout
import BalancedAssortments.NPStackSourceRecordsTotal

namespace BalancedAssortments.NPStack.SourceVerifier.Header
open NPStack NPStack.SourceVerifier DirectVerifier
open NPStackFields (dataFields)

inductive State | source (q : NPStackSourceRecords.State 8) | certificate (q : NPStackSourceRecords.State 2) |
  rank | revenue | one | done deriving DecidableEq,Fintype

def sourceMap : NPStackSourceRecords.Stack 8 → SourceVerifier.Stack
  | .input => .source | .scratch => .scratch | .field i => .body (sourceHeader i)
def certificateMap : NPStackSourceRecords.Stack 2 → SourceVerifier.Stack
  | .input => .certificate | .scratch => .scratch | .field i => .body (certificateHeader i)

def rankDen : BodyStack := .inr (.inl (.reg .rankDen false))
def revenueDen : BodyStack := .inr (.inl (.reg .revenueDen false))
def one : BodyStack := .inr (.inl (.reg .one false))

def program : Program SourceVerifier.Stack State where
  start := .source (NPStackSourceRecords.atIndex 8 0)
  inputStack := .source
  outputStack := .certificate
  code
    | .source .accept => .jump (.certificate (NPStackSourceRecords.atIndex 2 0))
    | .source q => ((NPStackSourceRecords.program 8).code q).rename sourceMap State.source
    | .certificate .accept => .jump .rank
    | .certificate q => ((NPStackSourceRecords.program 2).code q).rename certificateMap State.certificate
    | .rank => .push (.body rankDen) true .revenue
    | .revenue => .push (.body revenueDen) true .one
    | .one => .push (.body one) true .done
    | .done => .halt true

def sourceValues (s : Fin 8 → List Bool) : BodyStack → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (fun _ => []) (sourceHeader 0) (s 0)) (sourceHeader 1) (s 1)) (sourceHeader 2) (s 2))
      (sourceHeader 3) (s 3)) (sourceHeader 4) (s 4)) (sourceHeader 5) (s 5))
      (sourceHeader 6) (s 6)) (sourceHeader 7) (s 7)

def headerValues (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) : BodyStack → List Bool :=
  Function.update (Function.update (sourceValues s) (certificateHeader 0) (c 0)) (certificateHeader 1) (c 1)

def preparedValues (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) : BodyStack → List Bool :=
  Function.update (Function.update (Function.update (headerValues s c) rankDen [true]) revenueDen [true]) one [true]

def store (source certificate : List Bool) (values : BodyStack → List Bool) : SourceVerifier.Stack → List Bool
  | .source => source | .certificate => certificate | .scratch => [] | .body k => values k

def cfg (q : State) (source certificate : List Bool) (values : BodyStack → List Bool) : Config SourceVerifier.Stack State :=
  ⟨q,store source certificate values⟩

lemma sourceHeader_injective : Function.Injective sourceHeader := by
  intro i j h;fin_cases i <;> fin_cases j <;> simp_all [sourceHeader]
lemma certificateHeader_injective : Function.Injective certificateHeader := by
  intro i j h;fin_cases i <;> fin_cases j <;> simp_all [certificateHeader]
lemma sourceMap_injective : Function.Injective sourceMap := by
  intro a b h;cases a <;> cases b <;> simp_all [sourceMap,sourceHeader_injective.eq_iff]
lemma certificateMap_injective : Function.Injective certificateMap := by
  intro a b h;cases a <;> cases b <;> simp_all [certificateMap,certificateHeader_injective.eq_iff]

lemma source_code : CodeExtends (NPStackSourceRecords.program 8) program sourceMap State.source := by
  intro q h;cases q <;> simp_all [program,NPStackSourceRecords.program]
lemma certificate_code : CodeExtends (NPStackSourceRecords.program 2) program certificateMap State.certificate := by
  intro q h;cases q <;> simp_all [program,NPStackSourceRecords.program]

@[simp] lemma sourceValues_get (s : Fin 8 → List Bool) (i : Fin 8) : sourceValues s (sourceHeader i)=s i := by
  fin_cases i <;> simp [sourceValues,sourceHeader]

lemma sourceValues_outside (s : Fin 8 → List Bool) (k : BodyStack) (h : ∀ i,sourceHeader i≠k) : sourceValues s k=[] := by
  have hh : ∀ i,k≠sourceHeader i := fun i => (h i).symm
  simp [sourceValues,Function.update_apply,hh]

@[simp] lemma sourceValues_certificate (s : Fin 8 → List Bool) (i : Fin 2) : sourceValues s (certificateHeader i)=[] := by
  fin_cases i <;> simp [sourceValues,sourceHeader,certificateHeader]

@[simp] lemma headerValues_source (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (i : Fin 8) :
    headerValues s c (sourceHeader i)=s i := by
  fin_cases i <;> simp [headerValues,certificateHeader,sourceHeader,sourceValues]
@[simp] lemma headerValues_certificate (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (i : Fin 2) :
    headerValues s c (certificateHeader i)=c i := by
  fin_cases i <;> norm_num [headerValues,certificateHeader,Function.update_apply]

lemma headerValues_frame (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (k : BodyStack)
    (h : ∀ i,certificateHeader i≠k) : headerValues s c k=sourceValues s k := by
  have hh : ∀ i,k≠certificateHeader i := fun i => (h i).symm
  simp [headerValues,Function.update_apply,hh]

lemma source_run (s : Fin 8 → List Bool) (rest cert : List Bool) :
    Run program (NPStackSourceRecords.recordCost (List.ofFn s))
      (cfg (.source (NPStackSourceRecords.atIndex 8 0)) (dataFields (List.ofFn s)++rest) cert (fun _ => []))
      (cfg (.source .accept) rest cert (sourceValues s)) := by
  apply (NPStackSourceRecords.extract_record s rest).relocate_exact sourceMap State.source sourceMap_injective source_code
  · exact ⟨rfl,by intro k;cases k <;> rfl⟩
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [sourceMap,cfg,store,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · intro k hk
    cases k with
    | source => exact (hk .input rfl).elim
    | scratch => exact (hk .scratch rfl).elim
    | certificate => rfl
    | body k =>
      exact sourceValues_outside s k (fun i he => hk (.field i) (congrArg NPStackSourcePairing.Stack.body he))

lemma certificate_run (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (source rest : List Bool) :
    Run program (NPStackSourceRecords.recordCost (List.ofFn c))
      (cfg (.certificate (NPStackSourceRecords.atIndex 2 0)) source (dataFields (List.ofFn c)++rest) (sourceValues s))
      (cfg (.certificate .accept) source rest (headerValues s c)) := by
  apply (NPStackSourceRecords.extract_record c rest).relocate_exact certificateMap State.certificate certificateMap_injective certificate_code
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [certificateMap,cfg,store,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [certificateMap,cfg,store,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · intro k hk
    cases k with
    | source => rfl
    | scratch => exact (hk .scratch rfl).elim
    | certificate => exact (hk .input rfl).elim
    | body k =>
      exact headerValues_frame s c k (fun i he => hk (.field i) (congrArg NPStackSourcePairing.Stack.body he))

@[simp] lemma store_update_body (s c : List Bool) (values : BodyStack → List Bool) (k : BodyStack) (bits : List Bool) :
    Function.update (store s c values) (.body k) bits=store s c (Function.update values k bits) := by
  funext j;cases j <;> simp [store,Function.update_apply]

lemma initialize_run (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (source certificate : List Bool) :
    Run program 3 (cfg .rank source certificate (headerValues s c))
      (cfg .done source certificate (preparedValues s c)) := by
  have hrank : headerValues s c rankDen=[] := by simp [rankDen,headerValues,sourceValues,sourceHeader,certificateHeader]
  have hrev : (Function.update (headerValues s c) rankDen [true]) revenueDen=[] := by
    simp [rankDen,revenueDen,headerValues,sourceValues,sourceHeader,certificateHeader]
  have hone : (Function.update (Function.update (headerValues s c) rankDen [true]) revenueDen [true]) one=[] := by
    simp [rankDen,revenueDen,one,headerValues,sourceValues,sourceHeader,certificateHeader]
  have h1 : Step program (cfg .rank source certificate (headerValues s c))
      (cfg .revenue source certificate (Function.update (headerValues s c) rankDen [true])) := by
    simp [Step,successors,program,cfg,store,hrank]
  have h2 : Step program (cfg .revenue source certificate (Function.update (headerValues s c) rankDen [true]))
      (cfg .one source certificate (Function.update (Function.update (headerValues s c) rankDen [true]) revenueDen [true])) := by
    simp [Step,successors,program,cfg,store,hrev]
  have h3 : Step program (cfg .one source certificate (Function.update (Function.update (headerValues s c) rankDen [true]) revenueDen [true]))
      (cfg .done source certificate (preparedValues s c)) := by
    simp [Step,successors,program,cfg,store,hone,preparedValues]
  exact .succ h1 (.succ h2 (.one h3))

def headerCost (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) : ℕ :=
  NPStackSourceRecords.recordCost (List.ofFn s)+NPStackSourceRecords.recordCost (List.ofFn c)+5

lemma source_prefix (s : Fin 8 → List Bool) (rest cert : List Bool) :
    Run program (NPStackSourceRecords.recordCost (List.ofFn s)+1)
      (cfg (.source (NPStackSourceRecords.atIndex 8 0)) (dataFields (List.ofFn s)++rest) cert (fun _ => []))
      (cfg (.certificate (NPStackSourceRecords.atIndex 2 0)) rest cert (sourceValues s)) := by
  have hs : Step program (cfg (.source .accept) rest cert (sourceValues s))
      (cfg (.certificate (NPStackSourceRecords.atIndex 2 0)) rest cert (sourceValues s)) := by simp [Step,successors,program,cfg]
  exact (source_run s rest cert).trans (.one hs)

theorem header_run (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (sourceRest certificateRest : List Bool) :
    Run program (headerCost s c)
      (cfg (.source (NPStackSourceRecords.atIndex 8 0)) (dataFields (List.ofFn s)++sourceRest)
        (dataFields (List.ofFn c)++certificateRest) (fun _ => []))
      (cfg .done sourceRest certificateRest (preparedValues s c)) := by
  have hc : Step program (cfg (.certificate .accept) sourceRest certificateRest (headerValues s c))
      (cfg .rank sourceRest certificateRest (headerValues s c)) := by simp [Step,successors,program,cfg]
  have hh := (source_prefix s sourceRest (dataFields (List.ofFn c)++certificateRest)).trans
    ((certificate_run s c sourceRest certificateRest).trans (.succ hc (initialize_run s c sourceRest certificateRest)))
  convert hh using 1 <;> unfold headerCost <;> omega

end BalancedAssortments.NPStack.SourceVerifier.Header
