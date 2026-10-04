import BalancedAssortments.NPStackFields
import BalancedAssortments.NPCNFEncoding
import BalancedAssortments.NPStackDeterministic

namespace BalancedAssortments.NPSATStackThreeCheck
open NPStack NPCNF.Encoding

/-- The clause counter is part of finite control. No input integer controls a loop. -/
inductive Count where
  | zero | one | two | three
  deriving DecidableEq, Fintype

def Count.val : Count → ℕ
  | .zero => 0 | .one => 1 | .two => 2 | .three => 3

def Count.next : Count → Count
  | .zero => .one | .one => .two | .two => .three | .three => .three

inductive State where
  | formulaTag | formulaBit | formulaEnd (b : Bool)
  | clauseTag (n : Count) | signBit (n : Count) | signEnd (n : Count)
  | labelTag (n : Count) | labelBit (n : Count)
  | finish | accept | reject
  deriving DecidableEq, Fintype

def program : Program Unit State where
  code
    | .formulaTag => .pop () .reject .reject .formulaBit
    | .formulaBit => .pop () .reject (.formulaEnd false) (.formulaEnd true)
    | .formulaEnd false => .pop () .reject .finish .reject
    | .formulaEnd true => .pop () .reject (.clauseTag .zero) .reject
    | .clauseTag n => .pop () .reject .formulaTag (if n=.three then .reject else .signBit n.next)
    | .signBit n => .pop () .reject (.signEnd n) (.signEnd n)
    | .signEnd n => .pop () .reject (.labelTag n) .reject
    | .labelTag n => .pop () .reject (.clauseTag n) (.labelBit n)
    | .labelBit n => .pop () .reject (.labelTag n) (.labelTag n)
    | .finish => .pop () .accept .reject .reject
    | .accept => .halt true
    | .reject => .halt false
  start := .formulaTag
  inputStack := ()
  outputStack := ()

def cfg (q : State) (bits : List Bool) : Config Unit State := ⟨q,fun _ => bits⟩

@[simp] lemma update_unit (f : Unit → List Bool) (v : List Bool) :
    Function.update f () v=(fun _ => v) := by funext x; cases x; simp

@[simp] lemma tag_length (xs : List Bool) : (NPStackFields.tagBits xs).length=2*xs.length := by
  induction xs <;> simp [NPStackFields.tagBits, *,Nat.mul_add,Nat.add_assoc]; omega

lemma noChoice : NoChoice program := by
  intro q a b; cases q <;> simp [program]
  case formulaEnd b => cases b <;> simp [program]

lemma label_run (n : Count) (label suffix : List Bool) :
    Run program (2*label.length+1)
      (cfg (.labelTag n) (NPStackFields.tagBits label++false::suffix))
      (cfg (.clauseTag n) suffix) := by
  induction label with
  | nil => exact Run.one (by simp [Step,successors,program,cfg,NPStackFields.tagBits])
  | cons b bs ih =>
    have h1 : Step program (cfg (.labelTag n) (NPStackFields.tagBits (b::bs)++false::suffix))
        (cfg (.labelBit n) (b::(NPStackFields.tagBits bs++false::suffix))) := by
      simp [Step,successors,program,cfg,NPStackFields.tagBits]
    have h2 : Step program (cfg (.labelBit n) (b::(NPStackFields.tagBits bs++false::suffix)))
        (cfg (.labelTag n) (NPStackFields.tagBits bs++false::suffix)) := by
      cases b <;> simp [Step,successors,program,cfg]
    simpa [Nat.mul_add,Nat.add_assoc] using Run.succ h1 (Run.succ h2 ih)

lemma literal_run (n : Count) (hn : n≠.three) (l : BitLiteral) (suffix : List Bool) :
    Run program (2*l.labelBits.length+4)
      (cfg (.clauseTag n) (NPStackFields.dataFields [[l.positive],l.labelBits]++suffix))
      (cfg (.clauseTag n.next) suffix) := by
  have h1 : Step program
      (cfg (.clauseTag n) (NPStackFields.dataFields [[l.positive],l.labelBits]++suffix))
      (cfg (.signBit n.next) (l.positive::false::(NPStackFields.tagBits l.labelBits++false::suffix))) := by
    simp [Step,successors,program,cfg,NPStackFields.dataFields,NPStackFields.tagBits,hn]
  have h2 : Step program
      (cfg (.signBit n.next) (l.positive::false::(NPStackFields.tagBits l.labelBits++false::suffix)))
      (cfg (.signEnd n.next) (false::(NPStackFields.tagBits l.labelBits++false::suffix))) := by
    cases l.positive <;> simp [Step,successors,program,cfg]
  have h3 : Step program
      (cfg (.signEnd n.next) (false::(NPStackFields.tagBits l.labelBits++false::suffix)))
      (cfg (.labelTag n.next) (NPStackFields.tagBits l.labelBits++false::suffix)) := by
    simp [Step,successors,program,cfg]
  convert Run.succ h1 (Run.succ h2 (Run.succ h3 (label_run n.next l.labelBits suffix))) using 1 <;> omega

lemma clause_run (n : Count) (c : BitClause) (suffix : List Bool)
    (hn : n.val+c.length≤3) :
    Run program (NPStackFields.dataFields (clauseFields c)).length
      (cfg (.clauseTag n) (NPStackFields.dataFields (clauseFields c)++suffix))
      (cfg .formulaTag suffix) := by
  induction c generalizing n with
  | nil => exact Run.one (by simp [Step,successors,program,cfg,clauseFields,NPStackFields.dataFields,NPStackFields.tagBits])
  | cons l ls ih =>
    have hne : n≠.three := by intro he; subst n; simp [Count.val] at hn
    have hnext : n.next.val+ls.length≤3 := by cases n <;> simp_all only [Count.val,Count.next,List.length_cons] <;> omega
    have hh := (literal_run n hne l (NPStackFields.dataFields (clauseFields ls)++suffix)).trans (ih n.next hnext)
    convert hh using 1
    · simp only [clauseFields,NPStackFields.dataFields,List.flatMap_cons,List.append_assoc,List.length_append,List.length_cons,List.length_nil,tag_length]
      simp [NPStackFields.tagBits,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]; omega
    · simp [clauseFields,NPStackFields.dataFields,List.append_assoc]

lemma formula_run (F : BitFormula) (hF : ∀c∈F,c.length≤3) :
    Run program ((NPStackFields.dataFields (formulaFields F)).length+1)
      (cfg .formulaTag (NPStackFields.dataFields (formulaFields F))) (cfg .accept []) := by
  induction F with
  | nil =>
    have h1 : Step program (cfg .formulaTag [true,false,false]) (cfg .formulaBit [false,false]) := by simp [Step,successors,program,cfg]
    have h2 : Step program (cfg .formulaBit [false,false]) (cfg (.formulaEnd false) [false]) := by simp [Step,successors,program,cfg]
    have h3 : Step program (cfg (.formulaEnd false) [false]) (cfg .finish []) := by simp [Step,successors,program,cfg]
    have h4 : Step program (cfg .finish []) (cfg .accept []) := by simp [Step,successors,program,cfg]
    exact Run.succ h1 (Run.succ h2 (Run.succ h3 (Run.one h4)))
  | cons c cs ih =>
    have hc := clause_run .zero c (NPStackFields.dataFields (formulaFields cs)) (by simpa [Count.val] using hF c (by simp))
    have ht := ih (by intro x hx;exact hF x (by simp [hx]))
    have h1 : Step program (cfg .formulaTag (NPStackFields.dataFields (formulaFields (c::cs))))
        (cfg .formulaBit (true::false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs)))) := by
      simp [Step,successors,program,cfg,formulaFields,NPStackFields.dataFields,NPStackFields.tagBits,List.flatMap_append]
    have h2 : Step program
        (cfg .formulaBit (true::false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs))))
        (cfg (.formulaEnd true) (false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs)))) := by
      simp [Step,successors,program,cfg]
    have h3 : Step program
        (cfg (.formulaEnd true) (false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs))))
        (cfg (.clauseTag .zero) (NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs))) := by
      simp [Step,successors,program,cfg]
    convert Run.succ h1 (Run.succ h2 (Run.succ h3 (hc.trans ht))) using 1 <;>
      simp [formulaFields,NPStackFields.dataFields,NPStackFields.tagBits,List.flatMap_append,Nat.add_assoc]

lemma clause_length_cons (l : BitLiteral) (ls : BitClause) :
    (NPStackFields.dataFields (clauseFields (l::ls))).length=
      2*l.labelBits.length+4+(NPStackFields.dataFields (clauseFields ls)).length := by
  simp [clauseFields,NPStackFields.dataFields,NPStackFields.tagBits,List.length_flatMap]
  omega

lemma clause_reject (n : Count) (c : BitClause) (suffix : List Bool)
    (hn : 3<n.val+c.length) :
    ∃t≤(NPStackFields.dataFields (clauseFields c)).length,∃rest,
      Run program t (cfg (.clauseTag n) (NPStackFields.dataFields (clauseFields c)++suffix))
        (cfg .reject rest) := by
  induction c generalizing n with
  | nil => cases n <;> simp [Count.val] at hn
  | cons l ls ih =>
    by_cases hthree : n=.three
    · subst n
      refine ⟨1,?_,l.positive::false::(NPStackFields.tagBits l.labelBits++false::(NPStackFields.dataFields (clauseFields ls)++suffix)),Run.one ?_⟩
      · rw [clause_length_cons]; omega
      · simp [Step,successors,program,cfg,clauseFields,NPStackFields.dataFields,NPStackFields.tagBits,List.append_assoc]
    · have hnext : 3<n.next.val+ls.length := by
        cases n <;> simp_all [Count.val,Count.next] <;> omega
      obtain ⟨t,ht,rest,hr⟩ := ih n.next hnext
      refine ⟨2*l.labelBits.length+4+t,?_,rest,?_⟩
      · rw [clause_length_cons]; omega
      · simpa [clauseFields,NPStackFields.dataFields,List.append_assoc] using
          (literal_run n hthree l (NPStackFields.dataFields (clauseFields ls)++suffix)).trans hr

lemma formula_prefix (c : BitClause) (cs : BitFormula) :
    Run program 3 (cfg .formulaTag (NPStackFields.dataFields (formulaFields (c::cs))))
      (cfg (.clauseTag .zero) (NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs))) := by
  have h1 : Step program (cfg .formulaTag (NPStackFields.dataFields (formulaFields (c::cs))))
      (cfg .formulaBit (true::false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs)))) := by
    simp [Step,successors,program,cfg,formulaFields,NPStackFields.dataFields,NPStackFields.tagBits,List.flatMap_append]
  have h2 : Step program
      (cfg .formulaBit (true::false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs))))
      (cfg (.formulaEnd true) (false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs)))) := by
    simp [Step,successors,program,cfg]
  have h3 : Step program
      (cfg (.formulaEnd true) (false::(NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs))))
      (cfg (.clauseTag .zero) (NPStackFields.dataFields (clauseFields c)++NPStackFields.dataFields (formulaFields cs))) := by
    simp [Step,successors,program,cfg]
  exact Run.succ h1 (Run.succ h2 (Run.one h3))

lemma formula_length_cons (c : BitClause) (cs : BitFormula) :
    (NPStackFields.dataFields (formulaFields (c::cs))).length=
      3+(NPStackFields.dataFields (clauseFields c)).length+(NPStackFields.dataFields (formulaFields cs)).length := by
  simp [formulaFields,NPStackFields.dataFields,NPStackFields.tagBits,List.flatMap_append,Nat.add_assoc]; omega

lemma formula_reject (F : BitFormula) (hF : ¬∀c∈F,c.length≤3) :
    ∃t≤(NPStackFields.dataFields (formulaFields F)).length,∃rest,
      Run program t (cfg .formulaTag (NPStackFields.dataFields (formulaFields F))) (cfg .reject rest) := by
  induction F with
  | nil => simp at hF
  | cons c cs ih =>
    by_cases hc : c.length≤3
    · have ht : ¬∀c∈cs,c.length≤3 := by
        intro hall;apply hF;intro x hx;rcases List.mem_cons.mp hx with rfl|hx
        · exact hc
        · exact hall x hx
      obtain ⟨t,ht,rest,hr⟩ := ih ht
      have hcl := clause_run .zero c (NPStackFields.dataFields (formulaFields cs)) (by simpa [Count.val] using hc)
      refine ⟨3+(NPStackFields.dataFields (clauseFields c)).length+t,?_,rest,((formula_prefix c cs).trans hcl).trans hr⟩
      rw [formula_length_cons];omega
    · obtain ⟨t,ht,rest,hr⟩ := clause_reject .zero c (NPStackFields.dataFields (formulaFields cs)) (by simp [Count.val];omega)
      refine ⟨3+t,?_,rest,(formula_prefix c cs).trans hr⟩
      rw [formula_length_cons];omega

/-- On validated formula records, every accepting execution is precisely a
three-literal-per-clause check, including empty clauses and repeated literals. -/
theorem accepting_iff (F : BitFormula) :
    (∃t d,Run program t (cfg .formulaTag (NPStackFields.dataFields (formulaFields F))) d ∧ accepts program d)
      ↔ ∀c∈F,c.length≤3 := by
  constructor
  · rintro ⟨t,d,hr,ha⟩
    by_contra hn
    obtain ⟨u,hu,rest,hrej⟩ := formula_reject F hn
    have hh := hrej.halted_unique (noChoice_deterministic noChoice) hr rfl ha
    have he := congrArg (fun c => program.code c.pc) hh.2
    change Instr.halt false=program.code d.pc at he
    rw [ha] at he
    cases he
  · intro h
    exact ⟨_,_,formula_run F h,rfl⟩

end BalancedAssortments.NPSATStackThreeCheck
