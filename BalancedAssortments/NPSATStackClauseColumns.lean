import BalancedAssortments.NPSATStackClauseDigits

noncomputable section
namespace BalancedAssortments.NPSATStackClauseDigits
open NPStack NPStack.Structured NPCNF.Encoding ComplexityTimeBinary NPStackFields

def formulaBody (polarity : Bool) : Block Reg :=
  .seq (.atom (taggedReadAtom .input .scratch .sign))
    (.branch .sign (.atom rejectAtom) .skip
      (.seq (clause polarity 3 .zero) (.push .sign true)))

def formulaLoop (polarity : Bool) : Block Reg := .loop .sign (.atom rejectAtom) (formulaBody polarity)
def formula (polarity : Bool) : Block Reg := .seq (.push .sign true) (formulaLoop polarity)
def clauseDigit (query : List Bool) (polarity : Bool) (c : BitClause) : List Bool :=
  (advance query polarity .zero c).val.bits

def formulaBudget (query : List Bool) (F : BitFormula) : ℕ :=
  20*(F.length+1)+(F.map (budget query)).sum

lemma formulaLoop_exec (polarity : Bool) (query : List Bool) (F : BitFormula) (out : List Bool)
    (hF : ∀c∈F,c.length≤3) :
    ∃t≤formulaBudget query F,Exec (formulaLoop polarity)
      (store (dataFields (formulaFields F)) query [] [] [] [] [true] out)
      (store [] query [] [] [] [] [] (dataFields (F.map (clauseDigit query polarity)).reverse++out)) t := by
  induction F generalizing out with
  | nil =>
    have hr := read_sign false query [] out
    have hb : Exec (.branch Reg.sign (.atom rejectAtom) .skip
        (.seq (clause polarity 3 .zero) (.push .sign true)))
        (store [] query [] [] [] [] [false] out) (store [] query [] [] [] [] [] out) 3 := by
      apply Exec.branch_false (k := Reg.sign) (s := store [] query [] [] [] [] [false] out) (bs := []) rfl
      simpa using Exec.skip (store [] query [] [] [] [] [] out)
    have hbody := hr.seq hb
    have hnil : Exec (formulaLoop polarity) (store [] query [] [] [] [] [] out)
        (store [] query [] [] [] [] [] out) 1 := Exec.loop_nil rfl
    have hh := Exec.loop_true (k := Reg.sign) (f := .atom rejectAtom)
      (s := store [true,false,false] query [] [] [] [] [true] out) (bs := []) rfl
      (by simpa [formulaBody] using hbody) hnil
    refine ⟨16,by simp [formulaBudget],?_⟩
    simpa [formulaLoop,formulaFields,dataFields,tagBits] using hh
  | cons c cs ih =>
    have hc := hF c (by simp)
    have hcs : ∀c∈cs,c.length≤3 := by intro x hx;exact hF x (by simp [hx])
    obtain ⟨t,ht,hcl⟩ := clause_exec polarity 3 .zero query c (dataFields (formulaFields cs)) out hc
    obtain ⟨u,hu,hloop⟩ := ih (tagBits (clauseDigit query polarity c)++false::out) hcs
    have hp := Exec.push (store (dataFields (formulaFields cs)) query [] [] [] [] []
      (tagBits (clauseDigit query polarity c)++false::out)) Reg.sign true
    have hbranch : Exec
        (.branch Reg.sign (.atom rejectAtom) .skip
          (.seq (clause polarity 3 .zero) (.push .sign true)))
        (store (dataFields (clauseFields c)++dataFields (formulaFields cs)) query [] [] [] [] [true] out)
        (store (dataFields (formulaFields cs)) query [] [] [] [] [true]
          (tagBits (clauseDigit query polarity c)++false::out)) ((t+1+1)+2) := by
      apply Exec.branch_true (k := Reg.sign) (s := store (dataFields (clauseFields c)++dataFields (formulaFields cs)) query [] [] [] [] [true] out) (bs := []) rfl
      simpa only [update_sign,clauseDigit] using hcl.seq (by simpa [clauseDigit] using hp)
    have hread := read_sign true query (dataFields (clauseFields c)++dataFields (formulaFields cs)) out
    have hbody := hread.seq hbranch
    have hall := Exec.loop_true (k := Reg.sign) (f := .atom rejectAtom)
      (s := store (true::true::false::(dataFields (clauseFields c)++dataFields (formulaFields cs))) query [] [] [] [] [true] out)
      (bs := []) rfl (by simpa [formulaBody] using hbody) hloop
    refine ⟨(9+((t+1+1)+2)+1)+u+2,?_,?_⟩
    · simp only [formulaBudget,List.length_cons,List.map_cons,List.sum_cons] at hu ⊢
      omega
    · simpa [formulaLoop,formulaFields,dataFields,tagBits,List.reverse_cons,List.flatMap_append,List.append_assoc] using hall

/-- Concrete scan of clause records with a finite occurrence counter, emitting
reversed canonical digits and preserving the query label. -/
theorem clauseColumns_run (polarity : Bool) (query : List Bool) (F : BitFormula) (out : List Bool)
    (hF : ∀c∈F,c.length≤3) :
    ∃t≤formulaBudget query F+2,
      Run (Structured.program (formula polarity) Reg.input Reg.output) t
        ⟨entry (formula polarity),store (dataFields (formulaFields F)) query [] [] [] [] [] out⟩
        ⟨finish (formula polarity),store [] query [] [] [] [] []
          (dataFields (F.map (clauseDigit query polarity)).reverse++out)⟩ := by
  obtain ⟨t,ht,hr⟩ := formulaLoop_exec polarity query F out hF
  have hp := Exec.push (store (dataFields (formulaFields F)) query [] [] [] [] [] out) Reg.sign true
  have hall : Exec (formula polarity) (store (dataFields (formulaFields F)) query [] [] [] [] [] out)
      (store [] query [] [] [] [] [] (dataFields (F.map (clauseDigit query polarity)).reverse++out)) (1+t+1) := by
    exact hp.seq (by simpa using hr)
  exact ⟨1+t+1,by omega,hall.compiles Reg.input Reg.output⟩

lemma clauseDigit_value (query : List Bool) (polarity : Bool) (c : BitClause) (hc : c.length≤3) :
    value (clauseDigit query polarity c)=NPSATSubsetSum.occurrenceCount (value query) polarity c := by
  rw [clauseDigit,value_bits,advance_value query polarity .zero c (by simpa [NPSATStackThreeCheck.Count.val] using hc)]
  simp [NPSATStackThreeCheck.Count.val]

end BalancedAssortments.NPSATStackClauseDigits
