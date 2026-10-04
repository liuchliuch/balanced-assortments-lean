import BalancedAssortments.NPSATStackItem

noncomputable section
namespace BalancedAssortments.NPSATStackItem
open NPStack NPStack.Structured NPCNF.Encoding NPStackFields ComplexityTimeBinary

def itemDigits (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (polarity : Bool) : List (List Bool) :=
  (NPSATSubsetSum.variableColumns query catalog).1++F.map (NPSATStackClauseDigits.clauseDigit query polarity)

def itemBits (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (polarity : Bool) : List Bool :=
  (NPSATSubsetSum.packBits (itemDigits catalog F query polarity)).1

lemma itemDigits_length (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (polarity : Bool) :
    (itemDigits catalog F query polarity).length=catalog.length+F.length := by
  rw [itemDigits,← NPSATStackVariableColumns.digits_refine]
  simp

lemma itemDigits_width (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (polarity : Bool) :
    ∀d∈itemDigits catalog F query polarity,d.length≤3 := by
  intro d hd
  rw [itemDigits,← NPSATStackVariableColumns.digits_refine] at hd
  rcases List.mem_append.mp hd with hv|hc
  · obtain ⟨label,_,rfl⟩ := List.mem_map.mp hv
    unfold NPSATStackVariableColumns.digit
    split_ifs <;> simp
  · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hc
    unfold NPSATStackClauseDigits.clauseDigit
    have hval : (NPSATStackClauseDigits.advance query polarity .zero c).val≤3 := by
      generalize NPSATStackClauseDigits.advance query polarity .zero c=n
      cases n <;> decide
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hval

lemma itemBits_length (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (polarity : Bool) :
    (itemBits catalog F query polarity).length≤12*(catalog.length+F.length) := by
  have h := NPSATSubsetSum.packBits_length (itemDigits catalog F query polarity) 3
    (itemDigits_width catalog F query polarity)
  simpa [itemBits,itemDigits_length,Nat.mul_comm] using h

lemma itemBits_value (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (polarity : Bool)
    (hF : ∀c∈F,c.length≤3) :
    value (itemBits catalog F query polarity)=value (NPSATSubsetSum.variableItem catalog F query polarity).1 := by
  rw [itemBits,NPSATSubsetSum.packBits_value,NPSATSubsetSum.variableItem_value]
  congr 1
  simp only [itemDigits,List.map_append,NPSATSubsetSum.variableColumns_value,List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact NPSATStackClauseDigits.clauseDigit_value query polarity c (hF c hc)

def itemBudget (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (B : ℕ) : ℕ :=
  (5*(dataFields catalog).length+2)+54*(catalog.length+1)*(query.length+B+1)+
  (5*(dataFields (formulaFields F)).length+2)+(NPSATStackClauseDigits.formulaBudget query F+2)+
  1100*(catalog.length+F.length+1)*((catalog.length+F.length)*12+4)+
  (7*(12*(catalog.length+F.length))+6)+5

theorem item_exec (catalog : List (List Bool)) (F : BitFormula) (query wire : List Bool) (polarity : Bool)
    (B : ℕ) (hw : ∀label∈catalog,label.length≤B) (hF : ∀c∈F,c.length≤3) :
    ∃t ≤ itemBudget catalog F query B,Exec (item polarity)
      (store (dataFields catalog) (dataFields (formulaFields F)) query [] [] [] [] wire)
      (store (dataFields catalog) (dataFields (formulaFields F)) query [] [] [] []
        (FPTASCostProgram.serializeBits (itemBits catalog F query polarity)++wire)) t := by
  let cat := dataFields catalog
  let form := dataFields (formulaFields F)
  let ds := itemDigits catalog F query polarity
  let vb := dataFields (NPSATSubsetSum.variableColumns query catalog).1.reverse
  have hc := copyAtom_run (K := Reg) (.inr .catalog) (.inr .scratch) (.inr .catalogWork)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store cat form query [] [] [] [] wire) rfl
  have hcopy : Exec (.atom (copyAtom (.inr .catalog) (.inr .scratch) (.inr .catalogWork)))
      (store cat form query [] [] [] [] wire) (store cat form query cat [] [] [] wire) (5*cat.length+2) := by
    simpa only [store,List.append_nil,update_catalogWork] using hc
  obtain ⟨tv,htv,hv⟩ := variable_exec cat form query cat [] [] [] wire catalog rfl B hw
  have hv' : Exec (.atom variableAtom) (store cat form query cat [] [] [] wire)
      (store cat form query [] [] vb [] wire) tv := by simpa only [List.append_nil] using hv
  have hfc := copyAtom_run (K := Reg) (.inr .formula) (.inr .scratch) (.inr .formulaWork)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store cat form query [] [] vb [] wire) rfl
  have hfcopy : Exec (.atom (copyAtom (.inr .formula) (.inr .scratch) (.inr .formulaWork)))
      (store cat form query [] [] vb [] wire) (store cat form query [] form vb [] wire) (5*form.length+2) := by
    simpa only [store,List.append_nil,update_formulaWork] using hfc
  obtain ⟨tc,htc,hcl⟩ := clause_exec polarity cat form query [] vb [] wire F hF
  have hcl' : Exec (.atom (clauseAtom polarity)) (store cat form query [] form vb [] wire)
      (store cat form query [] [] (dataFields ds.reverse) [] wire) tc := by
    simpa [ds,itemDigits,vb,dataFields,List.reverse_append,List.flatMap_append] using hcl
  obtain ⟨tp,htp,hp⟩ := pack_exec cat form query [] [] wire ds (itemDigits_width catalog F query polarity)
  have he := encodeAtom_exec (K := Reg) (.inl .factor) (.inl .input) (.inl .pending) (.inr .wire)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.encodeMap])
    (store cat form query [] [] [] (NPSATSubsetSum.packBits ds).1 wire) rfl rfl
  have he' : Exec (.atom (encodeAtom (.inl .factor) (.inl .input) (.inl .pending) (.inr .wire)))
      (store cat form query [] [] [] (NPSATSubsetSum.packBits ds).1 wire)
      (store cat form query [] [] [] [] (FPTASCostProgram.serializeBits (itemBits catalog F query polarity)++wire))
      (7*(itemBits catalog F query polarity).length+6) := by
    simpa only [Macros.writes,store,update_number,update_wire,itemBits] using he
  have hall := hcopy.seq (hv'.seq (hfcopy.seq (hcl'.seq (hp.seq he'))))
  refine ⟨_,?_,hall⟩
  have hn := itemBits_length catalog F query polarity
  simp only [ds,itemDigits_length] at htp
  unfold itemBudget
  dsimp only [cat,form] at *
  omega

end BalancedAssortments.NPSATStackItem
