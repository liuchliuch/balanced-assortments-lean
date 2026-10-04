import BalancedAssortments.NPSATStackItemCorrect
import BalancedAssortments.NPStackStructuredUnary

noncomputable section
namespace BalancedAssortments.NPSATStackVariables
open NPStack NPStack.Structured NPCNF.Encoding NPStackFields ComplexityTimeBinary
abbrev Reg := NPSATStackItem.Reg ⊕ Unit

def query : Reg := .inl (.inr .query)
def wire : Reg := .inl (.inr .wire)
def scratch : Reg := .inl (.inr .scratch)
def remaining : Reg := .inr ()

def itemAtom (polarity : Bool) : Atom Reg :=
  embeddedAtom (Structured.program (NPSATStackItem.item polarity) (.inr .catalog) (.inr .wire))
    (finish (NPSATStackItem.item polarity)) (code_finish _) (program_noChoice _ _ _)
    Sum.inl (.inl (.inr .catalog)) wire

def body : Block Reg :=
  .seq (.atom (taggedReadAtom remaining scratch query))
    (.seq (.atom (itemAtom false)) (.seq (.atom (itemAtom true)) (clearStack query)))

def loop : Block Reg := .loop remaining
  (.seq (.push remaining false) body) (.seq (.push remaining true) body)

def store (rest catalog formula label out : List Bool) : Store Reg
  | .inl k => NPSATStackItem.store catalog formula label [] [] [] [] out k
  | .inr _ => rest

@[simp] lemma update_remaining (rest catalog formula label out v : List Bool) :
    Function.update (store rest catalog formula label out) remaining v=store v catalog formula label out := by
  funext k;rcases k with k|k <;> simp [remaining,store]
@[simp] lemma update_query (rest catalog formula label out v : List Bool) :
    Function.update (store rest catalog formula label out) query v=store rest catalog formula v out := by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> simp [query,store,NPSATStackItem.store]
  · simp [query,store]
@[simp] lemma update_wire (rest catalog formula label out v : List Bool) :
    Function.update (store rest catalog formula label out) wire v=store rest catalog formula label v := by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> simp [wire,store,NPSATStackItem.store]
  · simp [wire,store]

@[simp] lemma store_query (rest catalog formula label out : List Bool) : store rest catalog formula label out query=label := rfl
@[simp] lemma update_wire_raw (rest catalog formula label out v : List Bool) :
    Function.update (store rest catalog formula label out) (.inl (.inr NPSATStackItem.Extra.wire)) v=store rest catalog formula label v := update_wire _ _ _ _ _ _
@[simp] lemma update_query_raw (rest catalog formula label out v : List Bool) :
    Function.update (store rest catalog formula label out) (.inl (.inr NPSATStackItem.Extra.query)) v=store rest catalog formula v out := update_query _ _ _ _ _ _

def field (catalog : List (List Bool)) (F : BitFormula) (label : List Bool) (polarity : Bool) : List Bool :=
  FPTASCostProgram.serializeBits (NPSATStackItem.itemBits catalog F label polarity)

lemma item_exec (polarity : Bool) (catalog : List (List Bool)) (F : BitFormula) (rest label out : List Bool)
    (B : ℕ) (hw : ∀label∈catalog,label.length≤B) (hF : ∀c∈F,c.length≤3) :
    ∃t ≤ NPSATStackItem.itemBudget catalog F label B,Exec (.atom (itemAtom polarity))
      (store rest (dataFields catalog) (dataFields (formulaFields F)) label out)
      (store rest (dataFields catalog) (dataFields (formulaFields F)) label (field catalog F label polarity++out)) t := by
  obtain ⟨t,ht,hr⟩ := NPSATStackItem.item_exec catalog F label out polarity B hw hF
  refine ⟨t,ht,?_⟩
  have hh := embeddedAtom_exec_writes
    (Structured.program (NPSATStackItem.item polarity) (.inr .catalog) (.inr .wire))
    (finish (NPSATStackItem.item polarity)) (code_finish _) (program_noChoice _ _ _)
    Sum.inl Sum.inl_injective (.inl (.inr .catalog)) wire
    (hr.compiles (.inr .catalog) (.inr .wire))
    (store rest (dataFields catalog) (dataFields (formulaFields F)) label out) (by intro a;rfl)
    [(Sum.inr NPSATStackItem.Extra.wire,field catalog F label polarity++out)]
    (by simp [Macros.writes,NPSATStackItem.update_wire,field])
  simpa only [itemAtom,Macros.writes,List.map_cons,List.map_nil,update_wire_raw] using hh

lemma body_exec (catalog : List (List Bool)) (F : BitFormula) (label rest out : List Bool)
    (B : ℕ) (hw : ∀label∈catalog,label.length≤B) (hF : ∀c∈F,c.length≤3) :
    ∃t≤2*NPSATStackItem.itemBudget catalog F label B+8*label.length+8,
      Exec body (store (tagBits label++false::rest) (dataFields catalog) (dataFields (formulaFields F)) [] out)
        (store rest (dataFields catalog) (dataFields (formulaFields F)) []
          (field catalog F label true++field catalog F label false++out)) t := by
  have hh := taggedReadAtom_exec remaining scratch query (by decide) (by decide) (by decide)
    (store (tagBits label++false::rest) (dataFields catalog) (dataFields (formulaFields F)) [] out) label rest rfl rfl
  have hr : Exec (.atom (taggedReadAtom remaining scratch query))
      (store (tagBits label++false::rest) (dataFields catalog) (dataFields (formulaFields F)) [] out)
      (store rest (dataFields catalog) (dataFields (formulaFields F)) label out) (5*label.length+4) := by
    simpa only [update_remaining,update_query,store_query,List.append_nil] using hh
  obtain ⟨t,ht,hn⟩ := item_exec false catalog F rest label out B hw hF
  obtain ⟨u,hu,hp⟩ := item_exec true catalog F rest label (field catalog F label false++out) B hw hF
  have hc := clearStack_exec query
    (store rest (dataFields catalog) (dataFields (formulaFields F)) label
      (field catalog F label true++(field catalog F label false++out)))
  have hall := hr.seq (hn.seq (hp.seq hc))
  refine ⟨(5*label.length+4)+(t+(u+(3*label.length+1)+1)+1)+1,by omega,?_⟩
  simpa [body,store_query,update_query,List.append_assoc] using hall

def output (catalog : List (List Bool)) (F : BitFormula) : List (List Bool) → List Bool → List Bool
  | [],out => out
  | label::labels,out => output catalog F labels (field catalog F label true++field catalog F label false++out)

def budget (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) (B : ℕ) : ℕ :=
  (labels.map (fun label => 2*NPSATStackItem.itemBudget catalog F label B+8*label.length+14)).sum+1

lemma loop_exec (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) (out : List Bool)
    (B : ℕ) (hw : ∀label∈catalog,label.length≤B) (hF : ∀c∈F,c.length≤3) :
    ∃t ≤ budget catalog F labels B,Exec loop
      (store (dataFields labels) (dataFields catalog) (dataFields (formulaFields F)) [] out)
      (store [] (dataFields catalog) (dataFields (formulaFields F)) [] (output catalog F labels out)) t := by
  induction labels generalizing out with
  | nil =>
    refine ⟨1,by simp [budget],?_⟩
    exact Exec.loop_nil rfl
  | cons label labels ih =>
    obtain ⟨t,ht,hbody⟩ := body_exec catalog F label (dataFields labels) out B hw hF
    obtain ⟨u,hu,hloop⟩ := ih (field catalog F label true++field catalog F label false++out)
    have hfull : Exec loop
        (store (dataFields (label::labels)) (dataFields catalog) (dataFields (formulaFields F)) [] out)
        (store [] (dataFields catalog) (dataFields (formulaFields F)) [] (output catalog F (label::labels) out))
        ((1+t+1)+u+2) := by
      cases label with
      | nil =>
        have hp := Exec.push
          (store (dataFields labels) (dataFields catalog) (dataFields (formulaFields F)) [] out) remaining false
        have hr : Exec (.seq (.push remaining false) body)
            (store (dataFields labels) (dataFields catalog) (dataFields (formulaFields F)) [] out)
            (store (dataFields labels) (dataFields catalog) (dataFields (formulaFields F)) []
              (field catalog F [] true++field catalog F [] false++out)) (1+t+1) := by
          exact hp.seq (by simpa [tagBits] using hbody)
        have hh := Exec.loop_false (k := remaining) (t := .seq (.push remaining true) body)
          (s := store (false::dataFields labels) (dataFields catalog) (dataFields (formulaFields F)) [] out) rfl
          (by simpa using hr) hloop
        simpa [loop,dataFields,tagBits,output] using hh
      | cons b bs =>
        have hp := Exec.push
          (store (b::(tagBits bs++false::dataFields labels)) (dataFields catalog) (dataFields (formulaFields F)) [] out) remaining true
        have hr : Exec (.seq (.push remaining true) body)
            (store (b::(tagBits bs++false::dataFields labels)) (dataFields catalog) (dataFields (formulaFields F)) [] out)
            (store (dataFields labels) (dataFields catalog) (dataFields (formulaFields F)) []
              (field catalog F (b::bs) true++field catalog F (b::bs) false++out)) (1+t+1) := by
          exact hp.seq (by simpa [tagBits] using hbody)
        have hh := Exec.loop_true (k := remaining) (f := .seq (.push remaining false) body)
          (s := store (true::b::(tagBits bs++false::dataFields labels)) (dataFields catalog) (dataFields (formulaFields F)) [] out) rfl
          (by simpa using hr) hloop
        simpa [loop,dataFields,tagBits,output] using hh
    refine ⟨(1+t+1)+u+2,?_,hfull⟩
    simp only [budget,List.map_cons,List.sum_cons] at hu ⊢
    omega

def variableFields (catalog : List (List Bool)) (F : BitFormula) : List (List Bool) → List (List Bool)
  | [] => []
  | label::labels => NPSATStackItem.itemBits catalog F label false::NPSATStackItem.itemBits catalog F label true::variableFields catalog F labels

lemma output_fields (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) (out : List Bool) :
    output catalog F labels out=(variableFields catalog F labels).reverse.flatMap FPTASCostProgram.serializeBits++out := by
  induction labels generalizing out with
  | nil => rfl
  | cons label labels ih => simp [output,variableFields,ih,List.reverse_cons,List.flatMap_append,field,List.append_assoc]

/-- The complete two-items-per-variable loop, including exact serialization,
runs over actual catalogue cells and never over the magnitude of labels. -/
theorem variableItems_run (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) (out : List Bool)
    (B : ℕ) (hw : ∀label∈catalog,label.length≤B) (hF : ∀c∈F,c.length≤3) :
    ∃t ≤ budget catalog F labels B,
      Run (Structured.program loop remaining wire) t
        ⟨entry loop,store (dataFields labels) (dataFields catalog) (dataFields (formulaFields F)) [] out⟩
        ⟨finish loop,store [] (dataFields catalog) (dataFields (formulaFields F)) []
          ((variableFields catalog F labels).reverse.flatMap FPTASCostProgram.serializeBits++out)⟩ := by
  obtain ⟨t,ht,hr⟩ := loop_exec catalog F labels out B hw hF
  exact ⟨t,ht,by simpa [output_fields] using hr.compiles remaining wire⟩

lemma variableFields_value (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool))
    (hF : ∀c∈F,c.length≤3) :
    (variableFields catalog F labels).map value=(NPSATSubsetSum.variableItems catalog F labels).1.map value := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
    simp only [variableFields,NPSATSubsetSum.variableItems,List.map_cons,ih]
    rw [NPSATStackItem.itemBits_value catalog F label false hF,NPSATStackItem.itemBits_value catalog F label true hF]

end BalancedAssortments.NPSATStackVariables
