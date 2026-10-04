import BalancedAssortments.NPSATStackAtoms
import BalancedAssortments.NPSATStackThreeCheck
import BalancedAssortments.NPSATSubsetSumBits

noncomputable section
namespace BalancedAssortments.NPSATStackClauseDigits
open NPStack NPStack.Structured NPCNF.Encoding ComplexityTimeBinary NPStackFields
abbrev Count := NPSATStackThreeCheck.Count

inductive Reg where
  | input | query | label | copied | scratch | test | sign | output
  deriving DecidableEq, Fintype

def store (input query label copied scratch test sign output : List Bool) : Store Reg
  | .input => input | .query => query | .label => label | .copied => copied
  | .scratch => scratch | .test => test | .sign => sign | .output => output

@[simp] lemma update_input (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .input v=store v query label copied scratch test sign output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_query (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .query v=store input v label copied scratch test sign output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_label (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .label v=store input query v copied scratch test sign output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_copied (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .copied v=store input query label v scratch test sign output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_scratch (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .scratch v=store input query label copied v test sign output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_test (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .test v=store input query label copied scratch v sign output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_sign (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .sign v=store input query label copied scratch test v output := by
  funext k;cases k <;> simp [store]

@[simp] lemma update_output (input query label copied scratch test sign output v : List Bool) :
    Function.update (store input query label copied scratch test sign output) .output v=store input query label copied scratch test sign v := by
  funext k;cases k <;> simp [store]

def pushWord : List Bool → Block Reg
  | [] => .skip
  | b::bs => .seq (pushWord bs) (.push .output b)

lemma pushWord_exec (bits : List Bool) (s : Store Reg) :
    Exec (pushWord bits) s (Function.update s .output (bits++s .output)) (2*bits.length+1) := by
  induction bits with
  | nil => simpa [pushWord] using Exec.skip s
  | cons b bs ih =>
    have hp := Exec.push (Function.update s .output (bs++s .output)) Reg.output b
    have hh := ih.seq hp
    simpa [pushWord,Function.update_idem,Nat.mul_add,Nat.add_assoc] using hh

def emitCount (n : Count) : Block Reg := pushWord (tagBits n.val.bits++[false])

def rejectAtom : Atom Reg where
  states := 2
  instructions q := .halt (q.val=1)
  start := 0
  exit := 1
  halted := rfl
  noChoice := by intro q a b;simp

def checkLabel : Block Reg :=
  .seq (.atom (taggedReadAtom .input .scratch .label))
    (.seq (.atom (copyAtom .query .scratch .copied))
      (.atom (equalAtom .copied .label .test)))

/-- The unrolling depth is the literal constant three in the exported program;
all occurrence counts are finite control labels. -/
def clause (polarity : Bool) : ℕ → Count → Block Reg
  | 0,n => .seq (.atom (taggedReadAtom .input .scratch .sign))
      (.branch .sign (emitCount n) (.atom rejectAtom) (.atom rejectAtom))
  | fuel+1,n =>
    let literal (sign : Bool) :=
      .seq checkLabel
        (.branch .test (.atom rejectAtom) (clause polarity fuel n)
          (clause polarity fuel (if sign=polarity then n.next else n)))
    .seq (.atom (taggedReadAtom .input .scratch .sign))
      (.branch .sign (emitCount n) (literal false) (literal true))

lemma count_next (n : Count) (h : n.val<3) : n.next.val=n.val+1 := by
  cases n <;> simp_all [NPSATStackThreeCheck.Count.val,NPSATStackThreeCheck.Count.next]

lemma emitCount_exec (n : Count) (input query out : List Bool) :
    ∃t≤15,Exec (emitCount n) (store input query [] [] [] [] [] out)
      (store input query [] [] [] [] [] (tagBits n.val.bits++false::out)) t := by
  have hh := pushWord_exec (tagBits n.val.bits++[false]) (store input query [] [] [] [] [] out)
  refine ⟨2*(tagBits n.val.bits++[false]).length+1,?_,?_⟩
  · have hv : n.val≤3 := by cases n <;> decide
    have hs : n.val.size≤n.val := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n.val))
    rw [List.length_append,List.length_cons,List.length_nil,NPSATStackThreeCheck.tag_length,Nat.size_eq_bits_len] 
    omega
  · simpa only [emitCount,update_output,store,List.append_assoc,List.singleton_append] using hh

lemma checkLabel_exec (query label rest out : List Bool) :
    Exec checkLabel (store (tagBits label++false::rest) query [] [] [] [] [] out)
      (store rest query [] [] [] [decide (value query=value label)] [] out)
      ((5*label.length+4)+((5*query.length+2)+(2*max query.length label.length+3)+1)+1) := by
  have hr := taggedReadAtom_exec Reg.input .scratch .label (by decide) (by decide) (by decide)
    (store (tagBits label++false::rest) query [] [] [] [] [] out) label rest rfl rfl
  have hread : Exec (.atom (taggedReadAtom Reg.input .scratch .label))
      (store (tagBits label++false::rest) query [] [] [] [] [] out)
      (store rest query label [] [] [] [] out) (5*label.length+4) := by
    simpa only [update_input,update_label,store,List.append_nil] using hr
  have hc := copyAtom_run Reg.query .scratch .copied
    (by intro a b h;cases a <;> cases b <;> simp_all [NPStack.Macros.copyMap])
    (store rest query label [] [] [] [] out) rfl
  have hcopy : Exec (.atom (copyAtom Reg.query .scratch .copied))
      (store rest query label [] [] [] [] out) (store rest query label query [] [] [] out) (5*query.length+2) := by
    simpa only [store,List.append_nil,update_copied] using hc
  have he := equalAtom_exec Reg.copied .label .test
    (by intro a b h;cases a <;> cases b <;> simp_all [NPStack.Macros.normalizeMap])
    (store rest query label query [] [] [] out)
  have heq : Exec (.atom (equalAtom Reg.copied .label .test))
      (store rest query label query [] [] [] out)
      (store rest query [] [] [] [decide (value query=value label)] [] out)
      (2*max query.length label.length+3) := by
    simpa only [NPStack.Macros.writes,store,update_copied,update_label,update_test] using he
  exact hread.seq (hcopy.seq heq)

def advance (query : List Bool) (polarity : Bool) : Count → BitClause → Count
  | n,[] => n
  | n,l::ls => advance query polarity
      (if value query=value l.labelBits ∧ l.positive=polarity then n.next else n) ls

def budget (query : List Bool) (c : BitClause) : ℕ :=
  100*(query.length+1)*(c.length+1)+100*(c.map (fun l => l.labelBits.length)).sum

lemma read_sign (sign : Bool) (query rest out : List Bool) :
    Exec (.atom (taggedReadAtom Reg.input .scratch .sign))
      (store (true::sign::false::rest) query [] [] [] [] [] out)
      (store rest query [] [] [] [] [sign] out) 9 := by
  have hr := taggedReadAtom_exec Reg.input .scratch .sign (by decide) (by decide) (by decide)
    (store (true::sign::false::rest) query [] [] [] [] [] out) [sign] rest rfl rfl
  simpa only [List.length_cons,List.length_nil,Nat.mul_zero,Nat.add_zero,Nat.reduceAdd,Nat.reduceMul,
    store,update_input,update_sign,List.append_nil] using hr

lemma empty_clause_exec (polarity : Bool) (fuel : ℕ) (n : Count) (query rest out : List Bool) :
    ∃t≤22,Exec (clause polarity fuel n) (store (false::rest) query [] [] [] [] [] out)
      (store rest query [] [] [] [] [] (tagBits n.val.bits++false::out)) t := by
  have hr := taggedReadAtom_exec Reg.input .scratch .sign (by decide) (by decide) (by decide)
    (store (false::rest) query [] [] [] [] [] out) [] rest rfl rfl
  have hread : Exec (.atom (taggedReadAtom Reg.input .scratch .sign))
      (store (false::rest) query [] [] [] [] [] out) (store rest query [] [] [] [] [] out) 4 := by
    simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add,store,update_input,update_sign,List.append_nil] using hr
  obtain ⟨t,ht,he⟩ := emitCount_exec n rest query out
  refine ⟨4+(t+2)+1,by omega,?_⟩
  cases fuel <;> exact hread.seq (Exec.branch_nil rfl he)

theorem clause_exec (polarity : Bool) (fuel : ℕ) (n : Count)
    (query : List Bool) (c : BitClause) (rest out : List Bool) (hf : c.length≤fuel) :
    ∃t≤budget query c,Exec (clause polarity fuel n)
      (store (dataFields (clauseFields c)++rest) query [] [] [] [] [] out)
      (store rest query [] [] [] [] [] (tagBits (advance query polarity n c).val.bits++false::out)) t := by
  induction c generalizing fuel n with
  | nil =>
    obtain ⟨t,ht,hr⟩ := empty_clause_exec polarity fuel n query rest out
    refine ⟨t,?_,?_⟩
    · simp only [budget,List.length_nil,List.map_nil,List.sum_nil,Nat.zero_add,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
      omega
    · simpa [clauseFields,dataFields,tagBits,advance] using hr
  | cons l ls ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      let next : Count := if value query=value l.labelBits ∧ l.positive=polarity then n.next else n
      obtain ⟨u,hu,hr⟩ := ih fuel next (by simpa using hf)
      let tail := dataFields (clauseFields ls)++rest
      let final := store rest query [] [] [] [] [] (tagBits (advance query polarity next ls).val.bits++false::out)
      have hb : Exec
          (.branch Reg.test (.atom rejectAtom) (clause polarity fuel n)
            (clause polarity fuel (if l.positive=polarity then n.next else n)))
          (store tail query [] [] [] [decide (value query=value l.labelBits)] [] out) final (u+2) := by
        by_cases he : value query=value l.labelBits
        · have hnext : next=(if l.positive=polarity then n.next else n) := by simp [next,he]
          apply Exec.branch_true (bs := []) (by simp [store,he])
          simpa only [update_test,final,tail,hnext] using hr
        · have hnext : next=n := by simp [next,he]
          apply Exec.branch_false (bs := []) (by simp [store,he])
          simpa only [update_test,final,tail,hnext] using hr
      have hl := (checkLabel_exec query l.labelBits tail out).seq hb
      have hs : Exec
          (.branch Reg.sign (emitCount n)
            (.seq checkLabel (.branch .test (.atom rejectAtom) (clause polarity fuel n)
              (clause polarity fuel (if false=polarity then n.next else n))))
            (.seq checkLabel (.branch .test (.atom rejectAtom) (clause polarity fuel n)
              (clause polarity fuel (if true=polarity then n.next else n)))))
          (store (tagBits l.labelBits++false::tail) query [] [] [] [] [l.positive] out) final
          (((5*l.labelBits.length+4)+((5*query.length+2)+(2*max query.length l.labelBits.length+3)+1)+1)+(u+2)+1+2) := by
        cases he : l.positive
        · apply Exec.branch_false (bs := []) (by simp [store,he])
          simpa only [update_sign,he] using hl
        · apply Exec.branch_true (bs := []) (by simp [store,he])
          simpa only [update_sign,he] using hl
      have hall := (read_sign l.positive query (tagBits l.labelBits++false::tail) out).seq hs
      refine ⟨9+((((5*l.labelBits.length+4)+((5*query.length+2)+(2*max query.length l.labelBits.length+3)+1)+1)+(u+2)+1)+2)+1,?_,?_⟩
      · have hm : max query.length l.labelBits.length≤query.length+l.labelBits.length := by omega
        simp only [budget,List.length_cons,List.map_cons,List.sum_cons] at hu ⊢
        nlinarith
      · simpa [clause,clauseFields,dataFields,tagBits,List.append_assoc,tail,final,advance,next] using hall

lemma advance_value (query : List Bool) (polarity : Bool) (n : Count) (c : BitClause)
    (hn : n.val+c.length≤3) :
    (advance query polarity n c).val=n.val+NPSATSubsetSum.occurrenceCount (value query) polarity c := by
  induction c generalizing n with
  | nil => simp [advance,NPSATSubsetSum.occurrenceCount]
  | cons l ls ih =>
    by_cases he : value query=value l.labelBits ∧ l.positive=polarity
    · have hnlt : n.val<3 := by simp only [List.length_cons] at hn;omega
      have hv := count_next n hnlt
      have ht : n.next.val+ls.length≤3 := by simp only [List.length_cons] at hn;omega
      rw [advance,if_pos he,ih n.next ht,hv]
      simp [NPSATSubsetSum.occurrenceCount,List.countP_cons,he.1.symm,he.2,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have ht : n.val+ls.length≤3 := by simp only [List.length_cons] at hn;omega
      rw [advance,if_neg he,ih n ht]
      have hne : ¬(value l.labelBits=value query ∧ l.positive=polarity) := by simpa [eq_comm] using he
      simp [NPSATSubsetSum.occurrenceCount,List.countP_cons,hne]

end BalancedAssortments.NPSATStackClauseDigits
