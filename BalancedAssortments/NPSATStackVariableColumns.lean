import BalancedAssortments.NPSATStackAtoms
import BalancedAssortments.NPSATSubsetSumConstruct

noncomputable section
namespace BalancedAssortments.NPSATStackVariableColumns
open NPStack NPStack.Structured ComplexityTimeBinary NPStackFields

inductive Reg where
  | input | query | label | copied | scratch | test | output
  deriving DecidableEq, Fintype

def store (input query label copied scratch test output : List Bool) : Store Reg
  | .input => input | .query => query | .label => label | .copied => copied
  | .scratch => scratch | .test => test | .output => output

@[simp] lemma update_input (input query label copied scratch test output v : List Bool) :
    Function.update (store input query label copied scratch test output) .input v=store v query label copied scratch test output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_query (input query label copied scratch test output v : List Bool) :
    Function.update (store input query label copied scratch test output) .query v=store input v label copied scratch test output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_label (input query label copied scratch test output v : List Bool) :
    Function.update (store input query label copied scratch test output) .label v=store input query v copied scratch test output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_copied (input query label copied scratch test output v : List Bool) :
    Function.update (store input query label copied scratch test output) .copied v=store input query label v scratch test output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_scratch (input query label copied scratch test output v : List Bool) :
    Function.update (store input query label copied scratch test output) .scratch v=store input query label copied v test output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_test (input query label copied scratch test output v : List Bool) :
    Function.update (store input query label copied scratch test output) .test v=store input query label copied scratch v output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_output (input query label copied scratch test output v : List Bool) :
    Function.update (store input query label copied scratch test output) .output v=store input query label copied scratch test v := by
  funext k;cases k <;> simp [store]

def emitOne : Block Reg := .seq (.push .output false) (.seq (.push .output true) (.push .output true))
def emitDigit : Block Reg := .branch .test .skip (.push .output false) emitOne

def body : Block Reg :=
  .seq (.atom (taggedReadAtom .input .scratch .label))
    (.seq (.atom (copyAtom .query .scratch .copied))
      (.seq (.atom (equalAtom .copied .label .test)) emitDigit))

def loop : Block Reg := .loop .input
  (.seq (.push .input false) body) (.seq (.push .input true) body)

def digit (query label : List Bool) : List Bool :=
  if value query=value label then [true] else []

lemma emit_run (input query output : List Bool) (b : Bool) :
    ∃t≤7,Exec emitDigit (store input query [] [] [] [b] output)
      (store input query [] [] [] [] (tagBits (if b then [true] else [])++false::output)) t := by
  cases b with
  | false =>
    refine ⟨3,by omega,?_⟩
    have hp := Exec.push (store input query [] [] [] [] output) Reg.output false
    have hh := Exec.branch_false (k := Reg.test) (e := Block.skip) (t := emitOne)
      (s := store input query [] [] [] [false] output) rfl (by simpa using hp)
    simpa [emitDigit,tagBits] using hh
  | true =>
    have h0 := Exec.push (store input query [] [] [] [] output) Reg.output false
    have h1 := Exec.push (store input query [] [] [] [] (false::output)) Reg.output true
    have h2 := Exec.push (store input query [] [] [] [] (true::false::output)) Reg.output true
    have he : Exec emitOne (store input query [] [] [] [] output)
        (store input query [] [] [] [] (true::true::false::output)) 5 := by
      simpa [emitOne] using h0.seq (by simpa using h1.seq (by simpa using h2))
    refine ⟨7,by omega,?_⟩
    have hh := Exec.branch_true (k := Reg.test) (e := Block.skip) (f := Block.push Reg.output false)
      (s := store input query [] [] [] [true] output) rfl (by simpa using he)
    simpa [emitDigit,tagBits] using hh

lemma body_run (query label rest out : List Bool) :
    ∃t≤50*(query.length+label.length+1),
      Exec body (store (tagBits label++false::rest) query [] [] [] [] out)
        (store rest query [] [] [] [] (tagBits (digit query label)++false::out)) t := by
  have hr := taggedReadAtom_exec Reg.input .scratch .label (by decide) (by decide) (by decide)
    (store (tagBits label++false::rest) query [] [] [] [] out) label rest rfl rfl
  have hread : Exec (.atom (taggedReadAtom Reg.input .scratch .label))
      (store (tagBits label++false::rest) query [] [] [] [] out)
      (store rest query label [] [] [] out) (5*label.length+4) := by
    simpa only [update_input,update_label,store,List.append_nil] using hr
  have hc := copyAtom_run Reg.query .scratch .copied
    (by intro a b h;cases a <;> cases b <;> simp_all [NPStack.Macros.copyMap])
    (store rest query label [] [] [] out) rfl
  have hcopy : Exec (.atom (copyAtom Reg.query .scratch .copied))
      (store rest query label [] [] [] out) (store rest query label query [] [] out) (5*query.length+2) := by
    simpa only [store,List.append_nil,update_copied] using hc
  have he := equalAtom_exec Reg.copied .label .test
    (by intro a b h;cases a <;> cases b <;> simp_all [NPStack.Macros.normalizeMap])
    (store rest query label query [] [] out)
  have heq : Exec (.atom (equalAtom Reg.copied .label .test))
      (store rest query label query [] [] out)
      (store rest query [] [] [] [decide (value query=value label)] out)
      (2*max query.length label.length+3) := by
    simpa only [NPStack.Macros.writes,store,update_copied,update_label,update_test] using he
  obtain ⟨t,ht,hem⟩ := emit_run rest query out (decide (value query=value label))
  refine ⟨(5*label.length+4)+((5*query.length+2)+((2*max query.length label.length+3)+t+1)+1)+1,?_,?_⟩
  · have hm : max query.length label.length≤query.length+label.length := by omega
    omega
  · simpa [body,digit] using hread.seq (hcopy.seq (heq.seq hem))

lemma loop_run (query : List Bool) (labels : List (List Bool)) (out : List Bool) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) :
    ∃t≤54*(labels.length+1)*(query.length+B+1),
      Exec loop (store (dataFields labels) query [] [] [] [] out)
        (store [] query [] [] [] [] (dataFields (labels.map (digit query)).reverse++out)) t := by
  induction labels generalizing out with
  | nil =>
    refine ⟨1,by simp;omega,?_⟩
    simpa [loop,dataFields] using (Exec.loop_nil (k := Reg.input)
      (f := .seq (.push .input false) body) (t := .seq (.push .input true) body)
      (s := store [] query [] [] [] [] out) rfl)
  | cons label labels ih =>
    have hd := hw label (by simp)
    have htail : ∀x∈labels,x.length≤B := by intro x hx;exact hw x (by simp [hx])
    obtain ⟨t,ht,hbody⟩ := body_run query label (dataFields labels) out
    obtain ⟨u,hu,hloop⟩ := ih (tagBits (digit query label)++false::out) htail
    have hfull : Exec loop (store (dataFields (label::labels)) query [] [] [] [] out)
        (store [] query [] [] [] [] (dataFields (labels.map (digit query)).reverse++(tagBits (digit query label)++false::out)))
        ((1+t+1)+u+2) := by
      cases label with
      | nil =>
        have hp := Exec.push (store (dataFields labels) query [] [] [] [] out) Reg.input false
        have hr : Exec (.seq (.push Reg.input false) body)
            (store (dataFields labels) query [] [] [] [] out)
            (store (dataFields labels) query [] [] [] [] (tagBits (digit query [])++false::out)) (1+t+1) := by
          exact hp.seq (by simpa [tagBits] using hbody)
        have hh := Exec.loop_false (k := Reg.input) (t := .seq (.push Reg.input true) body)
          (s := store (false::dataFields labels) query [] [] [] [] out) rfl (by simpa using hr) hloop
        simpa [loop,dataFields,tagBits] using hh
      | cons b bs =>
        have hp := Exec.push (store (b::(tagBits bs++false::dataFields labels)) query [] [] [] [] out) Reg.input true
        have hr : Exec (.seq (.push Reg.input true) body)
            (store (b::(tagBits bs++false::dataFields labels)) query [] [] [] [] out)
            (store (dataFields labels) query [] [] [] [] (tagBits (digit query (b::bs))++false::out)) (1+t+1) := by
          exact hp.seq (by simpa [tagBits] using hbody)
        have hh := Exec.loop_true (k := Reg.input) (f := .seq (.push Reg.input false) body)
          (s := store (true::b::(tagBits bs++false::dataFields labels)) query [] [] [] [] out) rfl (by simpa using hr) hloop
        simpa [loop,dataFields,tagBits] using hh
    refine ⟨(1+t+1)+u+2,?_,?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simpa [dataFields,List.reverse_cons,List.flatMap_append,List.append_assoc] using hfull

lemma digits_refine (query : List Bool) (labels : List (List Bool)) :
    labels.map (digit query)=(NPSATSubsetSum.variableColumns query labels).1 := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
    simp only [List.map_cons,NPSATSubsetSum.variableColumns,ih]
    congr 1
    have he := NPCNF.Encoding.compare_eq_iff label query
    by_cases hv : value query=value label
    · simp [digit,hv,he.mpr hv.symm]
    · have hne : (compareBits label query).1≠.eq := fun h => hv (he.mp h).symm
      simp [digit,hv,hne]

/-- A concrete finite program realizes all variable indicator digits, preserves
the query label, and emits the digits in the order required by the Horner loop. -/
theorem variableColumns_run (query : List Bool) (labels : List (List Bool)) (out : List Bool) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) :
    ∃t≤54*(labels.length+1)*(query.length+B+1),
      Run (Structured.program loop Reg.input Reg.output) t
        ⟨entry loop,store (dataFields labels) query [] [] [] [] out⟩
        ⟨finish loop,store [] query [] [] [] []
          (dataFields (NPSATSubsetSum.variableColumns query labels).1.reverse++out)⟩ := by
  obtain ⟨t,ht,hr⟩ := loop_run query labels out B hw
  refine ⟨t,ht,?_⟩
  simpa [digits_refine] using hr.compiles Reg.input Reg.output

end BalancedAssortments.NPSATStackVariableColumns
