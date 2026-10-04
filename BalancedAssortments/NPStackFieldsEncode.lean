import BalancedAssortments.NPStackFieldDataCorrect
import BalancedAssortments.NPStackEmbedding

/-! Two finite passes serialize a tagged list of fields without reversing bits
inside fields. Both passes expand the actual per-field stack subroutines. -/
namespace BalancedAssortments.NPStackFieldsEncode
open NPStack
open NPStackFields (tagBits dataFields)

inductive Stack | input | accumulator | payload | scratch | count | output
  deriving DecidableEq, Fintype
inductive State | probe (second : Bool) | restore (second bit : Bool) |
  read (second : Bool) (q : NPStackFieldData.ReadState) |
  emit (q : NPStackFieldData.EmitState) | encode (q : NPStackFieldEncode.State) | accept
  deriving DecidableEq, Fintype

def source (second : Bool) : Stack := if second then .accumulator else .input

def readStack (second : Bool) : NPStackFieldData.Stack → Stack
  | .input => source second
  | .scratch => .scratch
  | .output => .payload

def emitStack : NPStackFieldData.Stack → Stack
  | .input => .payload
  | .scratch => .scratch
  | .output => .accumulator

def encodeStack : NPStackFieldEncode.Stack → Stack
  | .input => .payload
  | .reversed => .scratch
  | .count => .count
  | .output => .output

def program : Program Stack State where
  start := .probe false
  inputStack := .input
  outputStack := .output
  code
    | .probe s => .pop (source s) (if s then .accept else .probe true) (.restore s false) (.restore s true)
    | .restore s b => .push (source s) b (.read s .tag)
    | .read s .accept => .jump (if s then .encode .scan else .emit .reverse)
    | .read _ .reject => .halt false
    | .read s q => (NPStackFieldData.readProgram.code q).rename (readStack s) (.read s)
    | .emit .accept => .jump (.probe false)
    | .emit q => (NPStackFieldData.emitProgram.code q).rename emitStack .emit
    | .encode .accept => .jump (.probe true)
    | .encode q => (NPStackFieldEncode.program.code q).rename encodeStack .encode
    | .accept => .halt true

def store (i a p s c o : List Bool) : Stack → List Bool
  | .input => i
  | .accumulator => a
  | .payload => p
  | .scratch => s
  | .count => c
  | .output => o

def cfg (q : State) (i a p s c o : List Bool) : Config Stack State := ⟨q,store i a p s c o⟩

lemma read_injective (s : Bool) : Function.Injective (readStack s) := by
  intro a b h; cases s <;> cases a <;> cases b <;> simp_all [readStack,source]
lemma emit_injective : Function.Injective emitStack := by
  intro a b h; cases a <;> cases b <;> simp_all [emitStack]
lemma encode_injective : Function.Injective encodeStack := by
  intro a b h; cases a <;> cases b <;> simp_all [encodeStack]

lemma read_code (s : Bool) : CodeExtends NPStackFieldData.readProgram program (readStack s) (.read s) := by
  intro q h;cases q <;> simp_all [program,NPStackFieldData.readProgram]
lemma emit_code : CodeExtends NPStackFieldData.emitProgram program emitStack .emit := by
  intro q h;cases q <;> simp_all [program,NPStackFieldData.emitProgram]
lemma encode_code : CodeExtends NPStackFieldEncode.program program encodeStack .encode := by
  intro q h;cases q <;> simp_all [program,NPStackFieldEncode.program]

lemma call_run {K Q : Type*} [DecidableEq K] {P : Program K Q}
    (fk : K → Stack) (fq : Q → State) (hinj : Function.Injective fk) (hc : CodeExtends P program fk fq)
    {t : ℕ} {a b : Config K Q} {c d : Config Stack State}
    (hr : Run P t a b) (ha : Relocated fk fq a c) (hb : Relocated fk fq b d) (hf : Frame fk c d) :
    Run program t c d := by
  obtain ⟨e,he,her,hef⟩ := hr.relocate fk fq hinj hc ha
  have hd := relocated_frame_unique fk fq her hb hef hf
  simpa only [hd] using he

lemma read_first (bits rest acc out : List Bool) :
    Run program (5*bits.length+2)
      (cfg (.read false .tag) (tagBits bits++false::rest) acc [] [] [] out)
      (cfg (.read false .accept) rest acc bits [] [] out) := by
  apply call_run (readStack false) (.read false) (read_injective false) (read_code false)
    (NPStackFieldData.read_field bits rest [])
  · refine ⟨rfl,?_⟩; intro k;cases k <;> rfl
  · refine ⟨rfl,?_⟩; intro k;cases k <;> simp [readStack,source,cfg,store,NPStackFieldData.readConfig,NPStackFieldData.dataStacks]
  · intro k hk;cases k <;> simp [cfg,store] <;>
      first | exact (hk .input rfl).elim | exact (hk .scratch rfl).elim | exact (hk .output rfl).elim

lemma emit_first (bits rest acc out : List Bool) :
    Run program (5*bits.length+3)
      (cfg (.emit .reverse) rest acc bits [] [] out)
      (cfg (.emit .accept) rest (tagBits bits++false::acc) [] [] [] out) := by
  apply call_run emitStack .emit emit_injective emit_code (NPStackFieldData.emit_field bits acc)
  · refine ⟨rfl,?_⟩; intro k;cases k <;> rfl
  · refine ⟨rfl,?_⟩; intro k;cases k <;> rfl
  · intro k hk;cases k <;> simp [cfg,store] <;>
      first | exact (hk .input rfl).elim | exact (hk .scratch rfl).elim | exact (hk .output rfl).elim

lemma read_second (bits rest out : List Bool) :
    Run program (5*bits.length+2)
      (cfg (.read true .tag) [] (tagBits bits++false::rest) [] [] [] out)
      (cfg (.read true .accept) [] rest bits [] [] out) := by
  apply call_run (readStack true) (.read true) (read_injective true) (read_code true)
    (NPStackFieldData.read_field bits rest [])
  · refine ⟨rfl,?_⟩; intro k;cases k <;> rfl
  · refine ⟨rfl,?_⟩; intro k;cases k <;> simp [readStack,source,cfg,store,NPStackFieldData.readConfig,NPStackFieldData.dataStacks]
  · intro k hk;cases k <;> simp [cfg,store] <;>
      first | exact (hk .input rfl).elim | exact (hk .scratch rfl).elim | exact (hk .output rfl).elim

lemma encode_second (bits rest out : List Bool) :
    Run program (7*bits.length+4)
      (cfg (.encode .scan) [] rest bits [] [] out)
      (cfg (.encode .accept) [] rest [] [] [] (List.replicate bits.length true++false::(bits++out))) := by
  apply call_run encodeStack .encode encode_injective encode_code (NPStackFieldEncode.encode_field bits out)
  · refine ⟨rfl,?_⟩; intro k;cases k <;> rfl
  · refine ⟨rfl,?_⟩; intro k;cases k <;> rfl
  · intro k hk;cases k <;> simp [cfg,store] <;>
      first | exact (hk .input rfl).elim | exact (hk .reversed rfl).elim | exact (hk .count rfl).elim | exact (hk .output rfl).elim

lemma probe_first (b : Bool) (rest acc out : List Bool) :
    Run program 2 (cfg (.probe false) (b::rest) acc [] [] [] out)
      (cfg (.read false .tag) (b::rest) acc [] [] [] out) := by
  have h1 : Step program (cfg (.probe false) (b::rest) acc [] [] [] out)
      (cfg (.restore false b) rest acc [] [] [] out) := by
    cases b <;> simp [Step,successors,program,cfg,store,source] <;> funext k <;> cases k <;> simp [store]
  have h2 : Step program (cfg (.restore false b) rest acc [] [] [] out)
      (cfg (.read false .tag) (b::rest) acc [] [] [] out) := by
    simp [Step,successors,program,cfg,store,source];funext k;cases k <;> simp [store]
  exact .succ h1 (.one h2)

lemma probe_second (b : Bool) (rest out : List Bool) :
    Run program 2 (cfg (.probe true) [] (b::rest) [] [] [] out)
      (cfg (.read true .tag) [] (b::rest) [] [] [] out) := by
  have h1 : Step program (cfg (.probe true) [] (b::rest) [] [] [] out)
      (cfg (.restore true b) [] rest [] [] [] out) := by
    cases b <;> simp [Step,successors,program,cfg,store,source] <;> funext k <;> cases k <;> simp [store]
  have h2 : Step program (cfg (.restore true b) [] rest [] [] [] out)
      (cfg (.read true .tag) [] (b::rest) [] [] [] out) := by
    simp [Step,successors,program,cfg,store,source];funext k;cases k <;> simp [store]
  exact .succ h1 (.one h2)

lemma tagged_nonempty (bits rest : List Bool) : ∃ b bs,tagBits bits++false::rest=b::bs := by
  cases bits with
  | nil => exact ⟨false,rest,rfl⟩
  | cons b bs => exact ⟨true,b::(tagBits bs++false::rest),rfl⟩

def volume (fields : List (List Bool)) : ℕ := (fields.map List.length).sum

def wireField (bits : List Bool) : List Bool := List.replicate bits.length true++false::bits

def wireFields (fields : List (List Bool)) : List Bool := fields.flatMap wireField

lemma first_record (bits rest acc out : List Bool) :
    Run program (10*bits.length+9)
      (cfg (.probe false) (tagBits bits++false::rest) acc [] [] [] out)
      (cfg (.probe false) rest (tagBits bits++false::acc) [] [] [] out) := by
  obtain ⟨b,bs,he⟩ := tagged_nonempty bits rest
  have h1 := probe_first b bs acc out
  rw [←he] at h1
  have h2 : Step program (cfg (.read false .accept) rest acc bits [] [] out)
      (cfg (.emit .reverse) rest acc bits [] [] out) := by simp [Step,successors,program,cfg]
  have h3 : Step program (cfg (.emit .accept) rest (tagBits bits++false::acc) [] [] [] out)
      (cfg (.probe false) rest (tagBits bits++false::acc) [] [] [] out) := by simp [Step,successors,program,cfg]
  have hh := h1.trans ((read_first bits rest acc out).trans
    (.succ h2 ((emit_first bits rest acc out).trans (.one h3))))
  convert hh using 1 <;> omega

lemma first_pass (fields : List (List Bool)) (acc out : List Bool) :
    Run program (10*volume fields+9*fields.length+1)
      (cfg (.probe false) (dataFields fields) acc [] [] [] out)
      (cfg (.probe true) [] (dataFields fields.reverse++acc) [] [] [] out) := by
  induction fields generalizing acc with
  | nil => apply Run.one;simp [Step,successors,program,cfg,store,source,dataFields,volume]
  | cons bits fs ih =>
    have hh := (first_record bits (dataFields fs) acc out).trans (ih (tagBits bits++false::acc))
    convert hh using 1 <;> simp [volume,dataFields,List.reverse_cons,List.flatMap_append,List.append_assoc] <;> omega

lemma second_record (bits rest out : List Bool) :
    Run program (12*bits.length+10)
      (cfg (.probe true) [] (tagBits bits++false::rest) [] [] [] out)
      (cfg (.probe true) [] rest [] [] [] (wireField bits++out)) := by
  obtain ⟨b,bs,he⟩ := tagged_nonempty bits rest
  have h1 := probe_second b bs out
  rw [←he] at h1
  have h2 : Step program (cfg (.read true .accept) [] rest bits [] [] out)
      (cfg (.encode .scan) [] rest bits [] [] out) := by simp [Step,successors,program,cfg]
  have h3 : Step program (cfg (.encode .accept) [] rest [] [] [] (wireField bits++out))
      (cfg (.probe true) [] rest [] [] [] (wireField bits++out)) := by simp [Step,successors,program,cfg]
  have he' : List.replicate bits.length true++false::(bits++out)=wireField bits++out := by
    simp [wireField,List.append_assoc]
  have hencode := encode_second bits rest out
  rw [he'] at hencode
  have hh := h1.trans ((read_second bits rest out).trans (.succ h2 (hencode.trans (.one h3))))
  convert hh using 1 <;> omega

lemma second_pass (fields : List (List Bool)) (out : List Bool) :
    Run program (12*volume fields+10*fields.length+1)
      (cfg (.probe true) [] (dataFields fields) [] [] [] out)
      (cfg .accept [] [] [] [] [] (wireFields fields.reverse++out)) := by
  induction fields generalizing out with
  | nil => apply Run.one;simp [Step,successors,program,cfg,store,source,dataFields,volume,wireFields]
  | cons bits fs ih =>
    have hh := (second_record bits (dataFields fs) out).trans (ih (wireField bits++out))
    convert hh using 1 <;> simp [volume,dataFields,wireFields,List.reverse_cons,List.flatMap_append,List.append_assoc] <;> omega

theorem encode_fields (fields : List (List Bool)) (suffix : List Bool) :
    Run program (22*volume fields+19*fields.length+2)
      (cfg (.probe false) (dataFields fields) [] [] [] [] suffix)
      (cfg .accept [] [] [] [] [] (wireFields fields++suffix)) := by
  have h1 := first_pass fields [] suffix
  simp only [List.append_nil] at h1
  have hh := h1.trans (second_pass fields.reverse suffix)
  simp only [List.reverse_reverse,List.length_reverse] at hh
  have hv : volume fields.reverse=volume fields := by simp [volume,List.map_reverse]
  rw [hv] at hh
  convert hh using 1 <;> omega

lemma program_deterministic : Deterministic program := by
  apply noChoice_deterministic
  intro q a b
  cases q with
  | probe s => simp [program]
  | restore s bit => simp [program]
  | read s q => cases q <;> simp [program,NPStackFieldData.readProgram,Instr.rename]
  | emit q => cases q <;> simp [program,NPStackFieldData.emitProgram,Instr.rename]
  | encode q => cases q <;> simp [program,NPStackFieldEncode.program,Instr.rename]
  | accept => simp [program]

/-- Every accepting execution on a tagged field list has the proved exact
wire output; no alternative execution or late acceptance changes the result. -/
theorem accepting_result (fields : List (List Bool)) (suffix : List Bool) {t : ℕ} {d : Config Stack State}
    (hr : Run program t (cfg (.probe false) (dataFields fields) [] [] [] [] suffix) d)
    (ha : accepts program d) :
    d=cfg .accept [] [] [] [] [] (wireFields fields++suffix) ∧ t=22*volume fields+19*fields.length+2 := by
  have hh := (encode_fields fields suffix).halted_unique program_deterministic hr rfl ha
  exact ⟨hh.2.symm,hh.1.symm⟩

lemma dataFields_length (fields : List (List Bool)) :
    (dataFields fields).length=2*volume fields+fields.length := by
  induction fields with
  | nil => rfl
  | cons bits fs ih =>
    simp only [dataFields,List.flatMap_cons,List.length_append,List.length_singleton,
      NPStackFieldData.tagBits_length] at ih ⊢
    simp only [volume,List.map_cons,List.sum_cons,List.length_cons]
    change _=2*(bits.length+volume fs)+(fs.length+1)
    omega

lemma wireFields_length (fields : List (List Bool)) :
    (wireFields fields).length=(dataFields fields).length := by
  rw [dataFields_length]
  induction fields with
  | nil => rfl
  | cons bits fs ih =>
    simp only [wireFields,List.flatMap_cons,List.length_append,wireField,List.length_replicate,
      List.length_cons] at ih ⊢
    simp only [volume,List.map_cons,List.sum_cons,List.length_cons]
    change _=2*(bits.length+volume fs)+(fs.length+1)
    omega

lemma encode_cost_linear (fields : List (List Bool)) :
    22*volume fields+19*fields.length+2 ≤ 19*(dataFields fields).length+2 := by
  rw [dataFields_length];omega

lemma initial_cfg (bits : List Bool) :
    initial program bits=cfg (.probe false) bits [] [] [] [] [] := by
  unfold initial program cfg
  congr 1
  funext k;cases k <;> simp [store]

/-- A finite transducer on the literal tagged input, with a linear input-size
clock and no hidden payload-length, reversal, or serialization primitive. -/
theorem fields_outputs (fields : List (List Bool)) :
    OutputsIn program (dataFields fields) (wireFields fields) (19*(dataFields fields).length+2) := by
  refine ⟨22*volume fields+19*fields.length+2,encode_cost_linear fields,
    cfg .accept [] [] [] [] [] (wireFields fields),?_,rfl,rfl⟩
  rw [initial_cfg]
  simpa using encode_fields fields []

def finiteProgram : FiniteProgram where
  K := Stack
  Q := State
  program := program

end BalancedAssortments.NPStackFieldsEncode
