import BalancedAssortments.NPStackMacroMultiplyRun
import BalancedAssortments.NPStackMacroDataRuns
import BalancedAssortments.NPSATSubsetSumBits

namespace BalancedAssortments.NPSATStackPack
open NPStack NPStack.Macros ComplexityTimeBinary

inductive Extra where | digits | digit deriving DecidableEq, Fintype
abbrev Reg := MulStack ⊕ Extra
inductive Stage where
  | scan | restore (b : Bool) | read | seed0 | seed1 | seed2 | seed3
  | multiply | clear | add | done | reject
  deriving DecidableEq, Fintype

def table : Stage → Macro Reg Stage
  | .scan => .pop (.inr .digits) .done (.restore false) (.restore true)
  | .restore b => .push (.inr .digits) b .read
  | .read => .taggedRead (.inr .digits) (.inl .input) (.inr .digit) .seed0 .reject
  | .seed0 => .push (.inl .input) true .seed1
  | .seed1 => .push (.inl .input) false .seed2
  | .seed2 => .push (.inl .input) true .seed3
  | .seed3 => .push (.inl .input) false .multiply
  | .multiply => .multiply Sum.inl .clear
  | .clear => .pop (.inl .factor) .add .clear .clear
  | .add => .add (.inr .digit) (.inl .output) (.inl .pending) (.inl .factor) false .scan
  | .done => .halt true
  | .reject => .halt false

def program : Program Reg (Label Stage) := compile table .scan (.inr .digits) (.inl .factor)
def cfg (q : Stage) (s : Reg → List Bool) : Config Reg (Label Stage) := ⟨.main q,s⟩
def store (ds d seed acc product : List Bool) : Reg → List Bool
  | .inr .digits => ds | .inr .digit => d
  | .inl .input => seed | .inl .factor => acc | .inl .output => product
  | _ => []

@[simp] lemma update_digits (ds d seed acc product v : List Bool) :
    Function.update (store ds d seed acc product) (.inr .digits) v=store v d seed acc product := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]
@[simp] lemma update_digit (ds d seed acc product v : List Bool) :
    Function.update (store ds d seed acc product) (.inr .digit) v=store ds v seed acc product := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]
@[simp] lemma update_input (ds d seed acc product v : List Bool) :
    Function.update (store ds d seed acc product) (.inl .input) v=store ds d v acc product := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]
@[simp] lemma update_factor (ds d seed acc product v : List Bool) :
    Function.update (store ds d seed acc product) (.inl .factor) v=store ds d seed v product := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]
@[simp] lemma update_output (ds d seed acc product v : List Bool) :
    Function.update (store ds d seed acc product) (.inl .output) v=store ds d seed acc v := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

lemma seed_run (ds d acc : List Bool) :
    Run program 4 (cfg .seed0 (store ds d [] acc []))
      (cfg .multiply (store ds d [false,true,false,true] acc [])) := by
  have h0 : Step program (cfg .seed0 (store ds d [] acc [])) (cfg .seed1 (store ds d [true] acc [])) := by simp [Step,successors,program,compile,code,table,cfg,store]
  have h1 : Step program (cfg .seed1 (store ds d [true] acc [])) (cfg .seed2 (store ds d [false,true] acc [])) := by simp [Step,successors,program,compile,code,table,cfg,store]
  have h2 : Step program (cfg .seed2 (store ds d [false,true] acc [])) (cfg .seed3 (store ds d [true,false,true] acc [])) := by simp [Step,successors,program,compile,code,table,cfg,store]
  have h3 : Step program (cfg .seed3 (store ds d [true,false,true] acc [])) (cfg .multiply (store ds d [false,true,false,true] acc [])) := by simp [Step,successors,program,compile,code,table,cfg,store]
  exact Run.succ h0 (Run.succ h1 (Run.succ h2 (Run.one h3)))

lemma clear_run (ds d acc product : List Bool) :
    Run program (acc.length+1) (cfg .clear (store ds d [] acc product))
      (cfg .add (store ds d [] [] product)) := by
  induction acc with
  | nil => exact Run.one (by simp [Step,successors,program,compile,code,table,cfg,store])
  | cons b bs ih =>
    apply Run.succ (d := cfg .clear (store ds d [] bs product)) ?_ ih
    cases b <;> simp [Step,successors,program,compile,code,table,cfg,store]

lemma arithmetic_run (ds d acc : List Bool) :
    ∃t≤1000*(d.length+acc.length+1),
      Run program t (cfg .seed0 (store ds d [] acc []))
        (cfg .scan (store ds [] [] (addCarry d (mulBits [false,true,false,true] acc).1 false).1 [])) := by
  obtain ⟨t,ht,hr⟩ := multiply_call table .scan (.inr .digits) (.inl .factor)
    (q := .multiply) (next := .clear) (regs := Sum.inl) rfl Sum.inl_injective
    (store ds d [false,true,false,true] acc []) (by intro k hk hi;cases k <;> simp_all [store])
  have hm : Run program t (cfg .multiply (store ds d [false,true,false,true] acc []))
      (cfg .clear (store ds d [] acc (mulBits [false,true,false,true] acc).1)) := by
    simpa only [program,cfg,writes,store,update_input,update_output] using hr
  have ha := add_call table .scan (.inr .digits) (.inl .factor)
    (q := .add) (next := .scan) rfl
    (show Function.Injective (addMap (K := Reg) (.inr Extra.digit) (.inl MulStack.output) (.inl .pending) (.inl .factor)) from by intro a b h;cases a <;> cases b <;> simp_all [addMap])
    (store ds d [] [] (mulBits [false,true,false,true] acc).1) rfl rfl
  have haa : Run program (5*max d.length (mulBits [false,true,false,true] acc).1.length+8)
      (cfg .add (store ds d [] [] (mulBits [false,true,false,true] acc).1))
      (cfg .scan (store ds [] [] (addCarry d (mulBits [false,true,false,true] acc).1 false).1 [])) := by
    simpa only [program,cfg,writes,store,update_digit,update_output,update_factor] using ha
  refine ⟨4+t+(acc.length+1)+(5*max d.length (mulBits [false,true,false,true] acc).1.length+8),?_,(((seed_run ds d acc).trans hm).trans (clear_run ds d acc _)).trans haa⟩
  have hw := mulBits_length [false,true,false,true] acc
  simp only [store,List.length_cons,List.length_nil] at ht
  unfold multiplicationBudget at ht
  simp only [List.length_cons,List.length_nil] at hw
  have hmax : max d.length (mulBits [false,true,false,true] acc).1.length≤d.length+acc.length+8 := by omega
  omega

lemma read_run (d rest acc : List Bool) :
    Run program (5*d.length+6)
      (cfg .scan (store (NPStackFields.tagBits d++false::rest) [] [] acc []))
      (cfg .seed0 (store rest d [] acc [])) := by
  have hr := taggedRead_call table .scan (.inr .digits) (.inl .factor)
    (q := .read) (yes := .seed0) (no := .reject) rfl (by decide) (by decide) (by decide)
    (store (NPStackFields.tagBits d++false::rest) [] [] acc []) d rest rfl rfl
  have hh : Run program (5*d.length+4)
      (cfg .read (store (NPStackFields.tagBits d++false::rest) [] [] acc []))
      (cfg .seed0 (store rest d [] acc [])) := by
    simpa only [program,cfg,update_digits,update_digit,store,List.append_nil] using hr
  have hp (b : Bool) (bs : List Bool) :
      Run program 2 (cfg .scan (store (b::bs) [] [] acc []))
        (cfg .read (store (b::bs) [] [] acc [])) := by
    have h1 : Step program (cfg .scan (store (b::bs) [] [] acc [])) (cfg (.restore b) (store bs [] [] acc [])) := by
      cases b <;> simp [Step,successors,program,compile,code,table,cfg,store]
    have h2 : Step program (cfg (.restore b) (store bs [] [] acc [])) (cfg .read (store (b::bs) [] [] acc [])) := by
      simp [Step,successors,program,compile,code,table,cfg,store]
    exact Run.succ h1 (Run.one h2)
  have hprobe : Run program 2
      (cfg .scan (store (NPStackFields.tagBits d++false::rest) [] [] acc []))
      (cfg .read (store (NPStackFields.tagBits d++false::rest) [] [] acc [])) := by
    cases d with
    | nil => exact hp false rest
    | cons b bs => exact hp true (b::(NPStackFields.tagBits bs++false::rest))
  convert hprobe.trans hh using 1 <;> omega

def stepBits (acc digit : List Bool) : List Bool :=
  (addCarry digit (mulBits [false,true,false,true] acc).1 false).1

lemma step_run (digit rest acc : List Bool) :
    ∃t≤1100*(digit.length+acc.length+1),
      Run program t (cfg .scan (store (NPStackFields.tagBits digit++false::rest) [] [] acc []))
        (cfg .scan (store rest [] [] (stepBits acc digit) [])) := by
  obtain ⟨t,ht,hr⟩ := arithmetic_run rest digit acc
  exact ⟨5*digit.length+6+t,by omega,(read_run digit rest acc).trans hr⟩

lemma step_width (acc digit : List Bool) : (stepBits acc digit).length≤acc.length+digit.length+9 := by
  have hm := mulBits_length [false,true,false,true] acc
  have ha := addCarry_length digit (mulBits [false,true,false,true] acc).1 false
  simp only [List.length_cons,List.length_nil] at hm
  unfold stepBits
  have hmax : max digit.length (mulBits [false,true,false,true] acc).1.length≤acc.length+digit.length+8 := by omega
  omega

/-- A polynomial bound for a real finite Horner loop. The input records are
consumed in most-significant-digit order, without decoded arithmetic. -/
theorem loop_run (digits : List (List Bool)) (acc : List Bool) (B : ℕ)
    (hw : ∀d∈digits,d.length≤B) :
    ∃t≤1100*(digits.length+1)*(acc.length+digits.length*(B+9)+B+1),
      Run program t (cfg .scan (store (NPStackFields.dataFields digits) [] [] acc []))
        (cfg .done (store [] [] [] (digits.foldl stepBits acc) [])) := by
  induction digits generalizing acc with
  | nil =>
    refine ⟨1,by simp;omega,Run.one ?_⟩
    simp [Step,successors,program,compile,code,table,cfg,store,NPStackFields.dataFields]
  | cons d ds ih =>
    have hd := hw d (by simp)
    have htail : ∀x∈ds,x.length≤B := by intro x hx;exact hw x (by simp [hx])
    obtain ⟨t,ht,hr⟩ := step_run d (NPStackFields.dataFields ds) acc
    obtain ⟨u,hu,hs⟩ := ih (stepBits acc d) htail
    refine ⟨t+u,?_,?_⟩
    · have hwidth := step_width acc d
      have hle : (stepBits acc d).length+ds.length*(B+9)+B+1≤acc.length+(ds.length+1)*(B+9)+B+1 := by nlinarith
      have hm := Nat.mul_le_mul_left (1100*(ds.length+1)) hle
      simp only [List.length_cons]
      nlinarith
    · simpa [NPStackFields.dataFields,List.append_assoc] using hr.trans hs

lemma fold_reverse_pack (digits : List (List Bool)) :
    digits.reverse.foldl stepBits []=(NPSATSubsetSum.packBits digits).1 := by
  rw [List.foldl_reverse]
  induction digits with
  | nil => rfl
  | cons d ds ih => simp only [List.foldr_cons,ih];rfl

/-- Exact operational realization of the previously reviewed raw gadget's
base-ten bit packer. The caller supplies reversed tagged digit records. -/
theorem pack_run (digits : List (List Bool)) (B : ℕ) (hw : ∀d∈digits,d.length≤B) :
    ∃t≤1100*(digits.length+1)*(digits.length*(B+9)+B+1),
      Run program t (cfg .scan (store (NPStackFields.dataFields digits.reverse) [] [] [] []))
        (cfg .done (store [] [] [] (NPSATSubsetSum.packBits digits).1 [])) := by
  obtain ⟨t,ht,hr⟩ := loop_run digits.reverse [] B (by simpa using hw)
  rw [fold_reverse_pack] at hr
  exact ⟨t,by simpa using ht,hr⟩

lemma noChoice : NoChoice program := compile_noChoice _ _ _ _

end BalancedAssortments.NPSATStackPack
