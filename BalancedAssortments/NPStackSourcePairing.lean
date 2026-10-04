import BalancedAssortments.NPStackSourceRecordsTotal

/-! Structural six/three record pairing. The row body is an explicit finite
stack program whose instructions are relocated into this finite table. It is
never a decoded arithmetic or predicate callback. -/
namespace BalancedAssortments.NPStackSourcePairing
open NPStack
open NPStackFields (dataFields)

inductive Stack (W : Type*) | source | certificate | scratch | body (k : Fin 9 ⊕ W)
  deriving DecidableEq, Fintype
inductive State (Q : Type*) | probe | restore (b : Bool) | exhausted |
  source (q : NPStackSourceRecords.State 6) | certificate (q : NPStackSourceRecords.State 3) |
  body (q : Q) | accept | reject
  deriving DecidableEq, Fintype

abbrev Row := Fin 9 → List Bool

def sourceIndex (i : Fin 6) : Fin 9 := ⟨i.val,by omega⟩
def certificateIndex (i : Fin 3) : Fin 9 := ⟨6+i.val,by omega⟩

def sourceStack {W : Type*} : NPStackSourceRecords.Stack 6 → Stack W
  | .input => .source
  | .scratch => .scratch
  | .field i => .body (.inl (sourceIndex i))
def certificateStack {W : Type*} : NPStackSourceRecords.Stack 3 → Stack W
  | .input => .certificate
  | .scratch => .scratch
  | .field i => .body (.inl (certificateIndex i))

def rowStore {W : Type*} (row : Row) (work : W → List Bool) : Fin 9 ⊕ W → List Bool
  | .inl i => row i
  | .inr w => work w

def program {W Q : Type*} (body : Program (Fin 9 ⊕ W) Q) : Program (Stack W) (State Q) where
  start := .probe
  inputStack := .source
  outputStack := .certificate
  code
    | .probe => .pop .source .exhausted (.restore false) (.restore true)
    | .restore b => .push .source b (.source (NPStackSourceRecords.atIndex 6 0))
    | .exhausted => .pop .certificate .accept .reject .reject
    | .source .accept => .jump (.certificate (NPStackSourceRecords.atIndex 3 0))
    | .source q => ((NPStackSourceRecords.program 6).code q).rename sourceStack .source
    | .certificate .accept => .jump (.body body.start)
    | .certificate q => ((NPStackSourceRecords.program 3).code q).rename certificateStack .certificate
    | .body q => match body.code q with
      | .halt true => .jump .probe
      | .halt false => .halt false
      | instr => instr.rename Stack.body State.body
    | .accept => .halt true
    | .reject => .halt false

def store {W : Type*} (s c scratch : List Bool) (row : Row) (work : W → List Bool) : Stack W → List Bool
  | .source => s
  | .certificate => c
  | .scratch => scratch
  | .body k => rowStore row work k

def cfg {W Q : Type*} (q : State Q) (s c scratch : List Bool) (row : Row) (work : W → List Bool) : Config (Stack W) (State Q) :=
  ⟨q,store s c scratch row work⟩

lemma source_injective {W : Type*} : Function.Injective (sourceStack (W:=W)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [sourceStack]
  rename_i i j
  congr 1
  apply Fin.ext
  exact congrArg (fun x : Fin 9 => x.val) h

lemma certificate_injective {W : Type*} : Function.Injective (certificateStack (W:=W)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [certificateStack]
  rename_i i j
  congr 1
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [certificateIndex] at hh
  omega

lemma source_code {W Q : Type*} (body : Program (Fin 9 ⊕ W) Q) :
    CodeExtends (NPStackSourceRecords.program 6) (program body) sourceStack .source := by
  intro q h;cases q <;> simp_all [program,NPStackSourceRecords.program]
lemma certificate_code {W Q : Type*} (body : Program (Fin 9 ⊕ W) Q) :
    CodeExtends (NPStackSourceRecords.program 3) (program body) certificateStack .certificate := by
  intro q h;cases q <;> simp_all [program,NPStackSourceRecords.program]
lemma body_code {W Q : Type*} (body : Program (Fin 9 ⊕ W) Q) :
    CodeExtends body (program body) Stack.body State.body := by
  intro q h
  cases he : body.code q <;> simp_all [program]

variable {W Q : Type*} [DecidableEq W]

lemma call_run {K R : Type*} [DecidableEq K] {P : Program K R}
    (body : Program (Fin 9 ⊕ W) Q) (fk : K → Stack W) (fq : R → State Q)
    (hinj : Function.Injective fk) (hc : CodeExtends P (program body) fk fq)
    {t : ℕ} {a b : Config K R} {c d : Config (Stack W) (State Q)}
    (hr : Run P t a b) (ha : Relocated fk fq a c) (hb : Relocated fk fq b d) (hf : Frame fk c d) :
    Run (program body) t c d := by
  obtain ⟨e,he,her,hef⟩ := hr.relocate fk fq hinj hc ha
  have hd := relocated_frame_unique fk fq her hb hef hf
  simpa only [hd] using he

def sourceRow (fields : Fin 6 → List Bool) : Row := fun i =>
  if h : i.val < 6 then fields ⟨i.val,h⟩ else []

def pairedRow (s : Fin 6 → List Bool) (c : Fin 3 → List Bool) : Row := fun i =>
  if h : i.val < 6 then s ⟨i.val,h⟩ else c ⟨i.val-6,by omega⟩

lemma extract_source (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool)
    (srest cert : List Bool) (work : W → List Bool) :
    Run (program body) (NPStackSourceRecords.recordCost (List.ofFn s))
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) (dataFields (List.ofFn s)++srest) cert [] (fun _ => []) work)
      (cfg (.source .accept) srest cert [] (sourceRow s) work) := by
  apply call_run body sourceStack State.source source_injective (source_code body)
    (NPStackSourceRecords.extract_record s srest)
  · refine ⟨rfl,?_⟩;intro k;cases k <;> rfl
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [sourceStack,cfg,store,rowStore,sourceRow,sourceIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · intro k hk
    cases k with
    | source => exact (hk .input rfl).elim
    | scratch => exact (hk .scratch rfl).elim
    | certificate => rfl
    | body k =>
      cases k with
      | inr w => rfl
      | inl i =>
        have hn : ¬i.val < 6 := by
          intro hi
          exact hk (.field ⟨i.val,hi⟩) (by congr 2)
        simp [cfg,store,rowStore,sourceRow,hn]

lemma extract_certificate (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool)
    (c : Fin 3 → List Bool) (srest crest : List Bool) (work : W → List Bool) :
    Run (program body) (NPStackSourceRecords.recordCost (List.ofFn c))
      (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest (dataFields (List.ofFn c)++crest) [] (sourceRow s) work)
      (cfg (.certificate .accept) srest crest [] (pairedRow s c) work) := by
  apply call_run body certificateStack State.certificate certificate_injective (certificate_code body)
    (NPStackSourceRecords.extract_record c crest)
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [certificateStack,cfg,store,rowStore,sourceRow,certificateIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [certificateStack,cfg,store,rowStore,pairedRow,certificateIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · intro k hk
    cases k with
    | source => rfl
    | scratch => exact (hk .scratch rfl).elim
    | certificate => exact (hk .input rfl).elim
    | body k =>
      cases k with
      | inr w => rfl
      | inl i =>
        have hi : i.val < 6 := by
          by_contra hn
          have he : certificateIndex ⟨i.val-6,by omega⟩=i := by apply Fin.ext;simp [certificateIndex];omega
          exact hk (.field ⟨i.val-6,by omega⟩) (by simp [certificateStack,he])
        simp [cfg,store,rowStore,pairedRow,sourceRow,hi]

lemma invoke_body (body : Program (Fin 9 ⊕ W) Q) (row row' : Row) (work work' : W → List Bool)
    (srest crest : List Bool) {t : ℕ} {q : Q}
    (hr : Run body t ⟨body.start,rowStore row work⟩ ⟨q,rowStore row' work'⟩) :
    Run (program body) t (cfg (.body body.start) srest crest [] row work)
      (cfg (.body q) srest crest [] row' work') := by
  apply call_run body Stack.body State.body (by intro a b h;cases h;rfl) (body_code body) hr
  · exact ⟨rfl,fun _ => rfl⟩
  · exact ⟨rfl,fun _ => rfl⟩
  · intro k hk;cases k with
    | source => rfl
    | certificate => rfl
    | scratch => rfl
    | body k => exact (hk k rfl).elim

lemma probe_record (body : Program (Fin 9 ⊕ W) Q) (b : Bool) (rest cert : List Bool)
    (work : W → List Bool) :
    Run (program body) 2 (cfg .probe (b::rest) cert [] (fun _ => []) work)
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) (b::rest) cert [] (fun _ => []) work) := by
  have h1 : Step (program body) (cfg .probe (b::rest) cert [] (fun _ => []) work)
      (cfg (.restore b) rest cert [] (fun _ => []) work) := by
    cases b <;> simp [Step,successors,program,cfg,store] <;> funext k <;> cases k <;> simp [store]
  have h2 : Step (program body) (cfg (.restore b) rest cert [] (fun _ => []) work)
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) (b::rest) cert [] (fun _ => []) work) := by
    simp [Step,successors,program,cfg,store];funext k;cases k <;> simp [store]
  exact .succ h1 (.one h2)

/-- One actual paired record invokes exactly the supplied finite body run.
Source/certificate suffixes and body workspace are protected by disjoint tracks. -/
theorem paired_record (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool) (c : Fin 3 → List Bool)
    (work work' : W → List Bool) (srest crest : List Bool) {t : ℕ} {q : Q}
    (hr : Run body t ⟨body.start,rowStore (pairedRow s c) work⟩ ⟨q,rowStore (fun _ => []) work'⟩)
    (ha : body.code q=.halt true) :
    Run (program body) (NPStackSourceRecords.recordCost (List.ofFn s)+
      NPStackSourceRecords.recordCost (List.ofFn c)+t+5)
      (cfg .probe (dataFields (List.ofFn s)++srest) (dataFields (List.ofFn c)++crest) [] (fun _ => []) work)
      (cfg .probe srest crest [] (fun _ => []) work') := by
  have hnon : dataFields (List.ofFn s)++srest≠[] := by
    have hl : 0<(dataFields (List.ofFn s)).length := by
      simp [dataFields]
    intro he
    have hh := congrArg List.length he
    simp only [List.length_append,List.length_nil] at hh
    omega
  obtain ⟨b,bs,hbs⟩ := List.exists_cons_of_ne_nil hnon
  have hprobe := probe_record body b bs (dataFields (List.ofFn c)++crest) work
  rw [←hbs] at hprobe
  have hs : Step (program body) (cfg (.source .accept) srest (dataFields (List.ofFn c)++crest) [] (sourceRow s) work)
      (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest (dataFields (List.ofFn c)++crest) [] (sourceRow s) work) := by
    simp [Step,successors,program,cfg]
  have hc : Step (program body) (cfg (.certificate .accept) srest crest [] (pairedRow s c) work)
      (cfg (.body body.start) srest crest [] (pairedRow s c) work) := by simp [Step,successors,program,cfg]
  have hb : Step (program body) (cfg (.body q) srest crest [] (fun _ => []) work')
      (cfg .probe srest crest [] (fun _ => []) work') := by simp [Step,successors,program,cfg,ha]
  have hall := hprobe.trans ((extract_source body s srest (dataFields (List.ofFn c)++crest) work).trans
    (.succ hs ((extract_certificate body s c srest crest work).trans
      (.succ hc ((invoke_body body (pairedRow s c) (fun _ => []) work work' srest crest hr).trans (.one hb))))))
  convert hall using 1 <;> omega

end BalancedAssortments.NPStackSourcePairing
