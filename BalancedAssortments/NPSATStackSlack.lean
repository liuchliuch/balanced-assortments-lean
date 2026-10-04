import BalancedAssortments.NPSATStackItem
import BalancedAssortments.NPStackStructuredUnary

noncomputable section
namespace BalancedAssortments.NPSATStackSlack
open NPStack NPStack.Structured NPStackFields ComplexityTimeBinary

inductive Extra | vars | clauses | pre | remaining | temporary | digits | digit | scratch | wire
  deriving DecidableEq,Fintype
abbrev Reg := MulStack ⊕ Extra

def store (vars clauses pre remaining temporary digits number wire : List Bool) : Store Reg
  | .inr .vars => vars | .inr .clauses => clauses | .inr .pre => pre
  | .inr .remaining => remaining | .inr .temporary => temporary | .inr .digits => digits
  | .inl .factor => number | .inr .wire => wire | _ => []

@[simp] lemma update_variables (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inr .vars) v=store v clauses pre remaining temporary digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_clauses (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inr .clauses) v=store vars v pre remaining temporary digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_prefix (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inr .pre) v=store vars clauses v remaining temporary digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_remaining (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inr .remaining) v=store vars clauses pre v temporary digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_temporary (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inr .temporary) v=store vars clauses pre remaining v digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_digits (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inr .digits) v=store vars clauses pre remaining temporary v number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_number (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inl .factor) v=store vars clauses pre remaining temporary digits v wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_wire (vars clauses pre remaining temporary digits number wire v : List Bool) :
    Function.update (store vars clauses pre remaining temporary digits number wire) (.inr .wire) v=store vars clauses pre remaining temporary digits number v := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

def packMap : NPSATStackPack.Reg → Reg
  | .inl k => .inl k | .inr .digits => .inr .digits | .inr .digit => .inr .digit
lemma packMap_injective : Function.Injective packMap := by
  intro a b h;rcases a with a|a <;> rcases b with b|b
  · simpa [packMap] using h
  · cases b <;> simp [packMap] at h
  · cases a <;> simp [packMap] at h
  · cases a <;> cases b <;> simp_all [packMap]
def packAtom : Atom Reg := embeddedAtom NPSATStackPack.program (.main .done) rfl NPSATStackPack.noChoice
  packMap (.inr .digits) (.inl .factor)
def emitNumber : Block Reg := .seq (.atom packAtom)
  (.atom (encodeAtom (.inl .factor) (.inl .input) (.inl .pending) (.inr .wire)))

/-- The word is a fixed part of the finite instruction table. -/
def pushWord {K : Type*} (k : K) : List Bool → Block K
  | [] => .skip
  | b::bs => .seq (pushWord k bs) (.push k b)

lemma pushWord_exec {K : Type*} [DecidableEq K] (k : K) (word : List Bool) (s : Store K) :
    Exec (pushWord k word) s (Function.update s k (word++s k)) (2*word.length+1) := by
  induction word with
  | nil => simpa using Exec.skip s
  | cons b bs ih =>
    have h := ih.seq (Exec.push (Function.update s k (bs++s k)) k b)
    simpa [pushWord,Function.update_idem,Nat.mul_add,Nat.add_assoc] using h

def constantColumns {K : Type*} (source target : K) (word : List Bool) : Block K :=
  .loop source (pushWord target word) (pushWord target word)

def copies (word : List Bool) (n : ℕ) : List Bool := (List.replicate n word).flatten

lemma copies_succ (word : List Bool) (n : ℕ) : copies word (n+1)=copies word n++word := by
  simp [copies,List.replicate_succ',List.flatten_append]

lemma constantColumns_exec {K : Type*} [DecidableEq K] (source target : K) (hne : source≠target)
    (word : List Bool) (s : Store K) :
    Exec (constantColumns source target word) s
      (Function.update (Function.update s source []) target (copies word (s source).length++s target))
      ((2*word.length+3)*(s source).length+1) := by
  generalize he : s source=xs
  induction xs generalizing s with
  | nil =>
    have hu : Function.update (Function.update s source []) target (copies word 0++s target)=s := by
      simp [copies,←he]
    simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add,hu] using (Exec.loop_nil (f:=pushWord target word) (t:=pushWord target word) he)
  | cons b bs ih =>
    let u := Function.update s source bs
    let v := Function.update u target (word++u target)
    have hu : u target=s target := Function.update_of_ne (Ne.symm hne) _ _
    have hv : v source=bs := by simp [v,u,Function.update,hne]
    have hi:=ih v hv
    have hout : Function.update (Function.update v source []) target (copies word bs.length++v target)=
        Function.update (Function.update s source []) target (copies word (bs.length+1)++s target) := by
      funext k
      by_cases hk : k=target
      · subst k;simp [v,hu,copies_succ,List.append_assoc]
      · by_cases hs : k=source
        · subst k;simp [Function.update,hne]
        · simp [v,u,Function.update,hk,hs]
    rw [hout] at hi
    have hb := pushWord_exec target word u
    have hall : Exec (constantColumns source target word) s
        (Function.update (Function.update s source []) target (copies word (bs.length+1)++s target)) ((2*word.length+1)+((2*word.length+3)*bs.length+1)+2) := by
      cases b
      · exact Exec.loop_false he hb hi
      · exact Exec.loop_true he hb hi
    convert hall using 1 <;> simp only [List.length_cons,Nat.mul_add,Nat.mul_one] <;> omega

def item (digit : List Bool) : Block Reg :=
  .seq (.atom (copyAtom (.inr .pre) (.inr .scratch) (.inr .digits)))
    (.seq (pushWord (.inr .digits) (tagBits digit++[false]))
      (.seq (.atom (copyAtom (.inr .remaining) (.inr .scratch) (.inr .digits))) emitNumber))
def slackBody : Block Reg := .seq (item [true]) (.seq (item [false,true]) (.push (.inr .pre) false))
def slackLoop : Block Reg := .loop (.inr .remaining) slackBody slackBody

def target : Block Reg :=
  .seq (.atom (copyAtom (.inr .vars) (.inr .scratch) (.inr .temporary)))
    (.seq (constantColumns (.inr .temporary) (.inr .digits) (tagBits [true]++[false]))
      (.seq (.atom (copyAtom (.inr .clauses) (.inr .scratch) (.inr .temporary)))
        (.seq (constantColumns (.inr .temporary) (.inr .digits) (tagBits [false,false,true]++[false])) emitNumber)))
def build : Block Reg :=
  .seq (.atom (copyAtom (.inr .vars) (.inr .scratch) (.inr .pre)))
    (.seq (.atom (copyAtom (.inr .clauses) (.inr .scratch) (.inr .remaining)))
      (.seq slackLoop (.seq (clearStack (.inr .pre)) target)))

def program := Structured.program build (.inr .vars) (.inr .wire)

lemma pack_exec (vars clauses pre remaining temporary wire : List Bool) (digits : List (List Bool))
    (hw : ∀d∈digits,d.length≤3) :
    ∃t≤1100*(digits.length+1)*(digits.length*12+4),Exec (.atom packAtom)
      (store vars clauses pre remaining temporary (dataFields digits.reverse) [] wire)
      (store vars clauses pre remaining temporary [] (NPSATSubsetSum.packBits digits).1 wire) t := by
  obtain ⟨t,ht,hr⟩ := NPSATStackPack.pack_run digits 3 hw
  refine ⟨t,by simpa using ht,?_⟩
  have hh := embeddedAtom_exec_writes NPSATStackPack.program (.main .done) rfl NPSATStackPack.noChoice packMap packMap_injective
    (.inr .digits) (.inl .factor) hr (store vars clauses pre remaining temporary (dataFields digits.reverse) [] wire)
    (by intro a;rcases a with a|a <;> cases a <;> rfl)
    [((Sum.inr NPSATStackPack.Extra.digits : NPSATStackPack.Reg),[]),((Sum.inl MulStack.factor : NPSATStackPack.Reg),(NPSATSubsetSum.packBits digits).1)]
    (by simp [Macros.writes])
  simpa only [packAtom,Macros.writes,List.map_cons,List.map_nil,packMap,update_digits,update_number] using hh

def emitBudget (n : ℕ) : ℕ := 1100*(n+1)*(n*12+4)+84*n+7
lemma emitNumber_exec (vars clauses pre remaining temporary wire : List Bool) (digits : List (List Bool))
    (hw : ∀d∈digits,d.length≤3) :
    ∃t≤emitBudget digits.length,Exec emitNumber
      (store vars clauses pre remaining temporary (dataFields digits.reverse) [] wire)
      (store vars clauses pre remaining temporary [] [] (FPTASCostProgram.serializeBits (NPSATSubsetSum.packBits digits).1++wire)) t := by
  obtain ⟨t,ht,hr⟩ := pack_exec vars clauses pre remaining temporary wire digits hw
  have he:=encodeAtom_exec (K:=Reg) (.inl .factor) (.inl .input) (.inl .pending) (.inr .wire)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.encodeMap])
    (store vars clauses pre remaining temporary [] (NPSATSubsetSum.packBits digits).1 wire) rfl rfl
  have he' : Exec (.atom (encodeAtom (.inl .factor) (.inl .input) (.inl .pending) (.inr .wire)))
      (store vars clauses pre remaining temporary [] (NPSATSubsetSum.packBits digits).1 wire)
      (store vars clauses pre remaining temporary [] [] (FPTASCostProgram.serializeBits (NPSATSubsetSum.packBits digits).1++wire))
      (7*(NPSATSubsetSum.packBits digits).1.length+6) := by
    simpa only [store,Macros.writes,update_number,update_wire] using he
  have hw' := NPSATSubsetSum.packBits_length digits 3 hw
  refine ⟨_,?_,hr.seq he'⟩
  unfold emitBudget
  omega

end BalancedAssortments.NPSATStackSlack
