import BalancedAssortments.NPStackGuessSound
import BalancedAssortments.NPStackSourceVerifierHeaderCorrect
import BalancedAssortments.NPStackFieldsCorrect

namespace BalancedAssortments.NPStack.SourceVerifier.Framing
open NPStack
open NPStackFields (dataFields)

inductive Extra | raw | count | reversed | accumulator deriving DecidableEq,Fintype
abbrev Stack := SourceVerifier.Stack ⊕ Extra
inductive State (Q : Type*) | parser (q : NPStackFields.State) | body (q : Q)
  deriving DecidableEq,Fintype

def raw : Stack := .inr .raw
def certificate : Stack := .inl .certificate

def parserMap : NPStackFields.Stack → Stack
  | .inl .input => .inr .raw
  | .inl .count => .inr .count
  | .inl .reversed => .inr .reversed
  | .inl .output => .inl .source
  | .inr _ => .inr .accumulator

lemma parserMap_injective : Function.Injective parserMap := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [parserMap]

def program {Q : Type*} (P : Program SourceVerifier.Stack Q) : Program Stack (State Q) where
  start := .parser .probe
  inputStack := raw
  outputStack := .inl P.outputStack
  code
    | .parser .accept => .jump (.body P.start)
    | .parser q => (NPStackFields.program.code q).rename parserMap State.parser
    | .body q => (P.code q).rename Sum.inl State.body

def rawStore (word candidate : List Bool) : Stack → List Bool
  | .inr .raw => word
  | .inl .certificate => candidate
  | _ => []

def typedStore (fields : List (List Bool)) (candidate : List Bool) : SourceVerifier.Stack → List Bool :=
  Header.store (dataFields fields) candidate (fun _ => [])

def readyStore (fields : List (List Bool)) (candidate : List Bool) : Stack → List Bool
  | .inl k => typedStore fields candidate k
  | .inr _ => []

def bodyInput {Q : Type*} (P : Program SourceVerifier.Stack Q) (fields : List (List Bool)) (candidate : List Bool) :
    Config SourceVerifier.Stack Q := ⟨P.start,typedStore fields candidate⟩

def rawInput {Q : Type*} (P : Program SourceVerifier.Stack Q) (word candidate : List Bool) : Config Stack (State Q) :=
  ⟨.parser .probe,rawStore word candidate⟩

lemma twoInput_raw {Q : Type*} (P : Program SourceVerifier.Stack Q) (word candidate : List Bool) :
    Guess.twoInput (program P) certificate word candidate=rawInput P word candidate := by
  unfold Guess.twoInput initial rawInput program
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> simp [rawStore,raw,certificate]
  | inr k => cases k <;> simp [rawStore,raw,certificate]

lemma certificate_ne_input {Q : Type*} (P : Program SourceVerifier.Stack Q) : certificate≠(program P).inputStack := by
  simp [certificate,program,raw]

lemma parser_extends {Q : Type*} (P : Program SourceVerifier.Stack Q) :
    CodeExtends NPStackFields.program (program P) parserMap State.parser := by
  intro q h
  cases q <;> first | exact False.elim (h true rfl) | rfl

lemma body_code {Q : Type*} (P : Program SourceVerifier.Stack Q) (q : Q) :
    (program P).code (.body q)=(P.code q).rename Sum.inl State.body := rfl

def parserCost (fields : List (List Bool)) : ℕ :=
  14*(fields.map List.length).sum+10*fields.length+2

lemma parserCost_bound (word : List Bool) (fields : List (List Bool))
    (h : (EncodingTime.parse word).1=some fields) : parserCost fields ≤ 10*word.length+2 := by
  rw [NPStackFields.parse_sound word fields h,NPStackFields.encoding_length]
  unfold parserCost
  omega

/-- A literal finite raw SOURCE parser. The candidate is already a guessed
tagged stream and is preserved exactly; no second raw parser is inserted. -/
lemma parser_prefix {Q : Type*} (P : Program SourceVerifier.Stack Q) (word candidate : List Bool)
    (fields : List (List Bool)) (hp : (EncodingTime.parse word).1=some fields) :
    DeterministicRun (program P) (parserCost fields+1) (rawInput P word candidate)
      ⟨.body P.start,readyStore fields candidate⟩ := by
  have hsource := NPStackFields.fields_run fields []
  simp only [List.length_nil,mul_zero,add_zero,List.reverse_nil,List.nil_append] at hsource
  rw [←NPStackFields.parse_sound word fields hp] at hsource
  have h := hsource.relocate_deterministic_exact NPStackFields.program_noChoice parserMap State.parser parserMap_injective (parser_extends P)
    (c' := rawInput P word candidate) (d' := ⟨.parser .accept,readyStore fields candidate⟩)
    ⟨rfl,by intro k;fin_cases k <;> rfl⟩
    ⟨rfl,by intro k;fin_cases k <;> rfl⟩
    (by
      intro k hk
      cases k with
      | inl k => cases k with
        | source => exact (hk (.inl .output) rfl).elim
        | certificate => rfl
        | scratch => rfl
        | body k => rfl
      | inr k => cases k with
        | raw => exact (hk (.inl .input) rfl).elim
        | count => exact (hk (.inl .count) rfl).elim
        | reversed => exact (hk (.inl .reversed) rfl).elim
        | accumulator => exact (hk (.inr ()) rfl).elim)
  have hs : Step (program P) ⟨.parser .accept,readyStore fields candidate⟩ ⟨.body P.start,readyStore fields candidate⟩ := by
    simp [Step,successors,program]
  exact h.trans (.one (uniqueStep_of_code (by intro a b;simp [program])) hs)

lemma body_complete {Q : Type*} (P : Program SourceVerifier.Stack Q) (fields : List (List Bool)) (candidate : List Bool)
    {T : ℕ} {e : Config SourceVerifier.Stack Q} (hr : Run P T (bodyInput P fields candidate) e) :
    ∃ d,Run (program P) T ⟨.body P.start,readyStore fields candidate⟩ d ∧
      Relocated Sum.inl State.body e d := by
  obtain ⟨d,hd,hrel,_⟩ := hr.relocate (R:=program P) Sum.inl State.body Sum.inl_injective (fun _ _ => rfl)
    (c' := ⟨.body P.start,readyStore fields candidate⟩) ⟨rfl,fun _ => rfl⟩
  exact ⟨d,hd,hrel⟩

lemma body_accepts {Q : Type*} (P : Program SourceVerifier.Stack Q)
    {e : Config SourceVerifier.Stack Q} {d : Config Stack (State Q)} (hrel : Relocated Sum.inl State.body e d)
    (ha : accepts P e) : accepts (program P) d := by
  unfold accepts
  rw [hrel.1,body_code,ha]
  rfl

/-- Raw-source framing plus the supplied literal two-stream verifier, with
linear framing overhead in actual input bits. -/
theorem framed_complete {Q : Type*} (P : Program SourceVerifier.Stack Q) (word candidate : List Bool)
    (fields : List (List Bool)) (hp : (EncodingTime.parse word).1=some fields)
    {T : ℕ} {e : Config SourceVerifier.Stack Q}
    (hr : Run P T (bodyInput P fields candidate) e) (ha : accepts P e) :
    ∃ t ≤ 10*word.length+3+T,∃ d,
      Run (program P) t (Guess.twoInput (program P) certificate word candidate) d ∧ accepts (program P) d := by
  obtain ⟨d,hd,hrel⟩ := body_complete P fields candidate hr
  have hfull := (parser_prefix P word candidate fields hp).toRun.trans hd
  refine ⟨parserCost fields+1+T,?_,d,?_,body_accepts P hrel ha⟩
  · have hh := parserCost_bound word fields hp;omega
  · simpa only [twoInput_raw] using hfull

/-- Tagged and wire certificate representations have the same bit length;
raw witness bounds therefore transfer to the guessed tagged word exactly. -/
lemma tagged_wire_length (fields : List (List Bool)) :
    (dataFields fields).length=(NPCNF.Encoding.encodeFields fields).length := by
  rw [NPStackFields.dataFields_length,NPStackFields.encoding_length]

end BalancedAssortments.NPStack.SourceVerifier.Framing
