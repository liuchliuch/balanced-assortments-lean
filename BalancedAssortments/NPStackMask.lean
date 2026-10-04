import BalancedAssortments.NPStackDeterministic
import BalancedAssortments.ComplexityTimeSourceParsing

namespace BalancedAssortments.NPStackMask
open NPStack
open ComplexityTimeBinary (value)

inductive State | head | tail (b : Bool) | emit (b : Bool) | accept | reject
  deriving DecidableEq, Fintype

def program : Program Bool State where
  start := .head
  inputStack := false
  outputStack := true
  code
    | .head => .pop false (.emit false) (.tail false) (.tail true)
    | .tail b => .pop false (.emit b) (.tail b) .reject
    | .emit b => .push true b .accept
    | .accept => .halt true
    | .reject => .halt false

def store (input output : List Bool) : Bool → List Bool := fun k => if k then output else input

def cfg (q : State) (input output : List Bool) : Config Bool State := ⟨q,store input output⟩

@[simp] lemma update_input (input output xs : List Bool) : Function.update (store input output) false xs=store xs output := by
  funext k;cases k <;> simp [store]
@[simp] lemma update_output (input output xs : List Bool) : Function.update (store input output) true xs=store input xs := by
  funext k;cases k <;> simp [store]

def maskValue : List Bool → Option Bool
  | [] => some false
  | b::bs => if bs.all (!·) then some b else none

lemma tail_zero (b : Bool) (bits out : List Bool) (h : ∀ x∈bits,x=false) :
    Run program (bits.length+2) (cfg (.tail b) bits out) (cfg .accept [] (b::out)) := by
  induction bits with
  | nil =>
    have h1 : Step program (cfg (.tail b) [] out) (cfg (.emit b) [] out) := by simp [Step,successors,program,cfg,store]
    have h2 : Step program (cfg (.emit b) [] out) (cfg .accept [] (b::out)) := by simp [Step,successors,program,cfg,store]
    exact .succ h1 (.one h2)
  | cons x xs ih =>
    have hx : x=false := h x (by simp)
    subst x
    have h1 : Step program (cfg (.tail b) (false::xs) out) (cfg (.tail b) xs out) := by simp [Step,successors,program,cfg,store]
    exact .succ h1 (ih (fun x hx => h x (by simp [hx])))

lemma mask_run (bits out : List Bool) (b : Bool) (h : maskValue bits=some b) :
    Run program (bits.length+2) (cfg .head bits out) (cfg .accept [] (b::out)) := by
  cases bits with
  | nil =>
    simp [maskValue] at h
    subst b
    have h1 : Step program (cfg .head [] out) (cfg (.emit false) [] out) := by simp [Step,successors,program,cfg,store]
    have h2 : Step program (cfg (.emit false) [] out) (cfg .accept [] (false::out)) := by simp [Step,successors,program,cfg,store]
    exact .succ h1 (.one h2)
  | cons x xs =>
    have hh : xs.all (!·)=true ∧ x=b := by simpa [maskValue] using h
    rcases hh with ⟨hx,rfl⟩
    have hzero : ∀ z∈xs,z=false := by
      intro z hz
      have hh := List.all_eq_true.mp hx z hz
      cases z <;> simp_all
    have h1 : Step program (cfg .head (x::xs) out) (cfg (.tail x) xs out) := by
      cases x <;> simp [Step,successors,program,cfg,store]
    exact .succ h1 (tail_zero x xs out hzero)

lemma tail_reject (b : Bool) (bits out : List Bool) (h : true∈bits) :
    ∃ t≤bits.length,∃ rest,Run program t (cfg (.tail b) bits out) (cfg .reject rest out) := by
  induction bits with
  | nil => simp at h
  | cons x xs ih =>
    cases x with
    | true =>
      refine ⟨1,by simp,xs,.one ?_⟩
      simp [Step,successors,program,cfg,store]
    | false =>
      obtain ⟨t,ht,rest,hr⟩ := ih (by simpa using h)
      refine ⟨t+1,by simp;omega,rest,.succ ?_ hr⟩
      simp [Step,successors,program,cfg,store]

lemma mask_reject (bits out : List Bool) (h : maskValue bits=none) :
    ∃ t≤bits.length,∃ rest,Run program t (cfg .head bits out) (cfg .reject rest out) := by
  cases bits with
  | nil => simp [maskValue] at h
  | cons x xs =>
    have hx : true∈xs := by
      by_contra hn
      have ha : xs.all (!·)=true := List.all_eq_true.mpr (by
        intro z hz;cases z <;> simp_all)
      simp [maskValue,ha] at h
    obtain ⟨t,ht,rest,hr⟩ := tail_reject x xs out hx
    refine ⟨t+1,by simp;omega,rest,.succ ?_ hr⟩
    cases x <;> simp [Step,successors,program,cfg,store]

lemma value_zero_iff (bits : List Bool) : value bits=0 ↔ ∀ b∈bits,b=false := by
  induction bits with
  | nil => simp [value]
  | cons b bs ih => cases b <;> simp [value,ih]

lemma maskValue_numeric (bits : List Bool) :
    maskValue bits=if value bits=0 then some false else if value bits=1 then some true else none := by
  cases bits with
  | nil => rfl
  | cons b bs =>
    have ha : bs.all (!·)=true ↔ value bs=0 := by
      rw [value_zero_iff,List.all_eq_true]
      constructor <;> intro h z hz <;> have hh := h z hz <;> cases z <;> simp_all
    by_cases hz : value bs=0
    · have hh := ha.mpr hz
      cases b <;> simp [maskValue,hh,value,hz]
    · have hh : bs.all (!·)=false := Bool.eq_false_iff.mpr (fun he => hz (ha.mp he))
      have hn : 0<value bs := Nat.pos_of_ne_zero hz
      cases b <;> simp [maskValue,hh,value,show 2*value bs≠0 by omega,show 2*value bs≠1 by omega,
        show 1+2*value bs≠0 by omega,show 1+2*value bs≠1 by omega]

lemma maskValue_parseMask (bits : List Bool) : maskValue bits=(ComplexityTimeSourceParsing.parseMask bits).1 := by
  rw [maskValue_numeric]
  have eqiff (xs ys : List Bool) : (ComplexityTimeBinary.compareBits xs ys).1=.eq ↔ value xs=value ys := by
    have h := ComplexityTimeBinary.compareBits_correct xs ys
    cases he : (ComplexityTimeBinary.compareBits xs ys).1 <;> simp_all [ComplexityTimeBinary.comparisonMeaning] <;> omega
  simp [ComplexityTimeSourceParsing.parseMask,eqiff,value]

lemma program_deterministic : Deterministic program := by
  apply noChoice_deterministic
  intro q a b;cases q <;> simp [program]

theorem accepting_result (bits out : List Bool) {t : ℕ} {d : Config Bool State}
    (hr : Run program t (cfg .head bits out) d) (ha : accepts program d) :
    ∃ b,maskValue bits=some b ∧ d=cfg .accept [] (b::out) ∧ t=bits.length+2 := by
  cases hp : maskValue bits with
  | none =>
    obtain ⟨u,_,rest,hu⟩ := mask_reject bits out hp
    exact False.elim (rejecting_run_excludes_acceptance program_deterministic hu rfl hr ha)
  | some b =>
    have hh := (mask_run bits out b hp).halted_unique program_deterministic hr rfl ha
    exact ⟨b,rfl,hh.2.symm,hh.1.symm⟩

end BalancedAssortments.NPStackMask
