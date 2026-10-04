import BalancedAssortments.NPSATStackSlack
import BalancedAssortments.NPSATStackZeroColumns

noncomputable section
namespace BalancedAssortments.NPSATStackSlack
open NPStack NPStack.Structured NPStackFields ComplexityTimeBinary

def slackDigits (pre remaining : ℕ) (digit : List Bool) : List (List Bool) :=
  List.replicate pre []++digit::List.replicate remaining []
def slackBits (pre remaining : ℕ) (digit : List Bool) : List Bool :=
  (NPSATSubsetSum.packBits (slackDigits pre remaining digit)).1

def itemBudget (n : ℕ) : ℕ := emitBudget (n+1)+5*n+25
lemma item_exec (vars clauses wire digit : List Bool) (p r : ℕ) (hd : digit.length ≤ 3) :
    ∃t ≤ itemBudget (p+r),Exec (item digit)
      (store vars clauses (List.replicate p false) (List.replicate r false) [] [] [] wire)
      (store vars clauses (List.replicate p false) (List.replicate r false) [] [] []
        (FPTASCostProgram.serializeBits (slackBits p r digit)++wire)) t := by
  let pre := List.replicate p false
  let rest := List.replicate r false
  let field := tagBits digit++[false]
  have h1:=copyAtom_run (K:=Reg) (.inr .pre) (.inr .scratch) (.inr .digits)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store vars clauses pre rest [] [] [] wire) rfl
  have hc1 : Exec (.atom (copyAtom (.inr .pre) (.inr .scratch) (.inr .digits)))
      (store vars clauses pre rest [] [] [] wire) (store vars clauses pre rest [] pre [] wire) (5*p+2) := by
    simpa only [store,pre,List.append_nil,update_digits,List.length_replicate] using h1
  have h2:=pushWord_exec (.inr Extra.digits : Reg) field (store vars clauses pre rest [] pre [] wire)
  have hp : Exec (pushWord (.inr .digits) field)
      (store vars clauses pre rest [] pre [] wire) (store vars clauses pre rest [] (field++pre) [] wire)
      (2*field.length+1) := by simpa only [store,update_digits] using h2
  have h3:=copyAtom_run (K:=Reg) (.inr .remaining) (.inr .scratch) (.inr .digits)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store vars clauses pre rest [] (field++pre) [] wire) rfl
  have hc2 : Exec (.atom (copyAtom (.inr .remaining) (.inr .scratch) (.inr .digits)))
      (store vars clauses pre rest [] (field++pre) [] wire) (store vars clauses pre rest [] (rest++field++pre) [] wire) (5*r+2) := by
    simpa only [store,rest,update_digits,List.length_replicate,List.append_assoc] using h3
  have hds : dataFields (slackDigits p r digit).reverse=rest++field++pre := by
    have hz (n : ℕ) : List.flatMap (fun bits => tagBits bits++[false]) (List.replicate n [])=List.replicate n false := NPSATStackZeroColumns.dataFields_zeroes n
    simp [slackDigits,List.reverse_append,dataFields,List.flatMap_append,hz,pre,rest,field,List.append_assoc]
  have hw : ∀d∈slackDigits p r digit,d.length ≤ 3 := by
    intro d h
    simp only [slackDigits,List.mem_append,List.mem_cons] at h
    rcases h with h|h|h
    · have he := List.eq_of_mem_replicate h;subst d;simp
    · subst d;exact hd
    · have he := List.eq_of_mem_replicate h;subst d;simp
  obtain ⟨t,ht,he⟩ := emitNumber_exec vars clauses pre rest [] wire (slackDigits p r digit) hw
  rw [hds] at he
  refine ⟨_,?_,hc1.seq (hp.seq (hc2.seq he))⟩
  have hf : field.length=2*digit.length+1 := by simp [field,NPStackFieldData.tagBits_length]
  have hlen : (slackDigits p r digit).length=p+r+1 := by simp [slackDigits];omega
  rw [hlen] at ht
  unfold itemBudget
  omega

def targetDigits (n m : ℕ) : List (List Bool) := List.replicate n [true]++List.replicate m [false,false,true]
def targetBits (n m : ℕ) : List Bool := (NPSATSubsetSum.packBits (targetDigits n m)).1

lemma copies_fields (digit : List Bool) (n : ℕ) : copies (tagBits digit++[false]) n=dataFields (List.replicate n digit) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copies,List.replicate_succ,dataFields] at *;simp_all [List.append_assoc]

lemma target_exec (n m : ℕ) (wire : List Bool) :
    ∃t ≤ emitBudget (n+m)+25*(n+m)+10,Exec target
      (store (List.replicate n false) (List.replicate m false) [] [] [] [] [] wire)
      (store (List.replicate n false) (List.replicate m false) [] [] [] [] []
        (FPTASCostProgram.serializeBits (targetBits n m)++wire)) t := by
  let vars := List.replicate n false
  let clauses := List.replicate m false
  let vd := dataFields (List.replicate n [true])
  let cd := dataFields (List.replicate m [false,false,true])
  have hc:=copyAtom_run (K:=Reg) (.inr .vars) (.inr .scratch) (.inr .temporary)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store vars clauses [] [] [] [] [] wire) rfl
  have hc1 : Exec (.atom (copyAtom (.inr .vars) (.inr .scratch) (.inr .temporary)))
      (store vars clauses [] [] [] [] [] wire) (store vars clauses [] [] vars [] [] wire) (5*n+2) := by
    simpa only [store,vars,clauses,update_temporary,List.append_nil,List.length_replicate] using hc
  have hv:=constantColumns_exec (.inr Extra.temporary : Reg) (.inr .digits) (by decide)
    (tagBits [true]++[false]) (store vars clauses [] [] vars [] [] wire)
  simp only [store] at hv
  rw [copies_fields] at hv
  have hcv : Exec (constantColumns (.inr .temporary) (.inr .digits) (tagBits [true]++[false]))
      (store vars clauses [] [] vars [] [] wire) (store vars clauses [] [] [] vd [] wire) (9*n+1) := by
    simpa [store,vars,clauses,vd,cd,update_temporary,update_digits,copies_fields,tagBits] using hv
  have hc:=copyAtom_run (K:=Reg) (.inr .clauses) (.inr .scratch) (.inr .temporary)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store vars clauses [] [] [] vd [] wire) rfl
  have hc2 : Exec (.atom (copyAtom (.inr .clauses) (.inr .scratch) (.inr .temporary)))
      (store vars clauses [] [] [] vd [] wire) (store vars clauses [] [] clauses vd [] wire) (5*m+2) := by
    simpa only [store,vars,clauses,update_temporary,List.append_nil,List.length_replicate] using hc
  have hh:=constantColumns_exec (.inr Extra.temporary : Reg) (.inr .digits) (by decide)
    (tagBits [false,false,true]++[false]) (store vars clauses [] [] clauses vd [] wire)
  simp only [store] at hh
  rw [copies_fields] at hh
  have hcc : Exec (constantColumns (.inr .temporary) (.inr .digits) (tagBits [false,false,true]++[false]))
      (store vars clauses [] [] clauses vd [] wire) (store vars clauses [] [] [] (cd++vd) [] wire) (17*m+1) := by
    simpa [store,vars,clauses,vd,cd,update_temporary,update_digits,copies_fields,tagBits] using hh
  have hds : dataFields (targetDigits n m).reverse=cd++vd := by
    simp [targetDigits,List.reverse_append,dataFields,cd,vd]
  have hw : ∀d∈targetDigits n m,d.length ≤ 3 := by
    intro d hd
    rcases List.mem_append.mp hd with h|h
    · have he:=List.eq_of_mem_replicate h;subst d;decide
    · have he:=List.eq_of_mem_replicate h;subst d;decide
  obtain ⟨t,ht,he⟩ := emitNumber_exec vars clauses [] [] [] wire (targetDigits n m) hw
  rw [hds] at he
  have hlen : (targetDigits n m).length=n+m := by simp [targetDigits]
  rw [hlen] at ht
  refine ⟨_,?_,hc1.seq (hcv.seq (hc2.seq (hcc.seq he)))⟩
  omega

end BalancedAssortments.NPSATStackSlack
