import BalancedAssortments.NPStackStructuredAtoms

/-! Static natural register names are compiled to a genuinely finite register
set. The bound is computed from the fixed finite control table, never from input
contents. No decoded input integer controls register allocation. -/
noncomputable section
namespace BalancedAssortments.NPStack
open NPStack

 def Instr.registerBound {Q : Type*} : Instr ℕ Q → ℕ
  | .push k _ _ => k+1
  | .pop k _ _ _ => k+1
  | _ => 0

def Instr.InBounds {Q : Type*} (N : ℕ) : Instr ℕ Q → Prop
  | .push k _ _ => k<N
  | .pop k _ _ _ => k<N
  | _ => True
lemma Instr.inBounds_of_bound {Q : Type*} (i : Instr ℕ Q) {N : ℕ} (h : i.registerBound≤N) : i.InBounds N := by
  cases i <;> simp_all [InBounds,registerBound] <;> omega

def Instr.restrict {Q : Type*} (N : ℕ) : Instr ℕ Q → Instr (Fin N) Q
  | .halt b => .halt b
  | .jump q => .jump q
  | .push k b q => if h : k<N then .push ⟨k,h⟩ b q else .halt false
  | .pop k e f t => if h : k<N then .pop ⟨k,h⟩ e f t else .halt false
  | .choice q r => .choice q r

namespace Structured

def restrictStore (N : ℕ) (s : ℕ → List Bool) : Fin N → List Bool := fun k => s k.val
lemma restrictStore_update {N k : ℕ} (hk : k<N) (s : ℕ → List Bool) (bits : List Bool) :
    restrictStore N (Function.update s k bits)=Function.update (restrictStore N s) ⟨k,hk⟩ bits := by
  funext i
  by_cases he : i.val=k
  · have hi : i=⟨k,hk⟩ := Fin.ext he
    subst i
    simp [restrictStore]
  · have hi : i≠⟨k,hk⟩ := fun h => he (congrArg Fin.val h)
    simp [restrictStore,Function.update,he,hi]

def restrictProgram {Q : Type*} (P : Program ℕ Q) (N : ℕ)
    (h : ∀ q,(P.code q).InBounds N) (hi : P.inputStack<N) (ho : P.outputStack<N) : Program (Fin N) Q :=
  ⟨fun q => (P.code q).restrict N,P.start,⟨P.inputStack,hi⟩,⟨P.outputStack,ho⟩⟩

lemma restrict_step {Q : Type*} (P : Program ℕ Q) (N : ℕ)
    (h : ∀ q,(P.code q).InBounds N) (hi : P.inputStack<N) (ho : P.outputStack<N)
    {q r : Q} {s t : ℕ → List Bool} (hs : Step P ⟨q,s⟩ ⟨r,t⟩) :
    Step (restrictProgram P N h hi ho) ⟨q,restrictStore N s⟩ ⟨r,restrictStore N t⟩ := by
  have hb := h q
  unfold Step successors at hs ⊢
  simp only [restrictProgram]
  cases hc : P.code q with
  | halt b => simp [hc] at hs
  | jump next =>
    simp only [hc,List.mem_singleton,Config.mk.injEq] at hs
    obtain ⟨rfl,rfl⟩ := hs
    simp [hc,Instr.restrict]
  | push k b next =>
    simp only [hc,List.mem_singleton,Config.mk.injEq] at hs
    obtain ⟨rfl,rfl⟩ := hs
    have hk : k<N := by simpa [hc,Instr.InBounds] using hb
    simp [hc,Instr.restrict,hk,restrictStore_update hk,restrictStore]
  | pop k empty onFalse onTrue =>
    have hk : k<N := by simpa [hc,Instr.InBounds] using hb
    cases hkval : s k with
    | nil =>
      simp only [hc,hkval,List.mem_singleton,Config.mk.injEq] at hs
      obtain ⟨rfl,rfl⟩ := hs
      simp [hc,Instr.restrict,hk,restrictStore,hkval]
    | cons b bs =>
      simp only [hc,hkval,List.mem_singleton,Config.mk.injEq] at hs
      obtain ⟨rfl,rfl⟩ := hs
      simp [hc,Instr.restrict,hk,restrictStore_update hk,restrictStore,hkval]
  | choice a b =>
    simp only [hc,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with hs|hs
    all_goals
      cases hs
      simp [hc,Instr.restrict]

lemma restrict_run {Q : Type*} (P : Program ℕ Q) (N : ℕ)
    (h : ∀ q,(P.code q).InBounds N) (hi : P.inputStack<N) (ho : P.outputStack<N)
    {n : ℕ} {c d : Config ℕ Q} (hr : Run P n c d) :
    Run (restrictProgram P N h hi ho) n ⟨c.pc,restrictStore N c.stk⟩ ⟨d.pc,restrictStore N d.stk⟩ := by
  induction hr with
  | zero c => exact .zero _
  | succ hs hr ih => exact .succ (restrict_step P N h hi ho hs) ih

variable {Q : Type*} [Fintype Q]
def finiteRegisterBound (P : Program ℕ Q) : ℕ :=
  1+P.inputStack+P.outputStack+∑ q,(P.code q).registerBound
lemma finiteRegisterBound_code (P : Program ℕ Q) (q : Q) : (P.code q).InBounds (finiteRegisterBound P) := by
  apply Instr.inBounds_of_bound
  have hh : (P.code q).registerBound≤∑ q,(P.code q).registerBound := Finset.single_le_sum (f := fun q : Q => (P.code q).registerBound) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  unfold finiteRegisterBound
  omega
lemma finiteRegisterBound_input (P : Program ℕ Q) : P.inputStack<finiteRegisterBound P := by unfold finiteRegisterBound;omega
lemma finiteRegisterBound_output (P : Program ℕ Q) : P.outputStack<finiteRegisterBound P := by unfold finiteRegisterBound;omega

def finitelyNamed (P : Program ℕ Q) : Program (Fin (finiteRegisterBound P)) Q :=
  restrictProgram P _ (finiteRegisterBound_code P) (finiteRegisterBound_input P) (finiteRegisterBound_output P)

lemma finitelyNamed_run (P : Program ℕ Q) {n : ℕ} {c d : Config ℕ Q} (h : Run P n c d) :
    Run (finitelyNamed P) n ⟨c.pc,restrictStore (finiteRegisterBound P) c.stk⟩
      ⟨d.pc,restrictStore (finiteRegisterBound P) d.stk⟩ := restrict_run P _ _ _ _ h

/-- Any fixed structured block with static natural register names yields a
finite-stack, finite-control primitive program. -/
def finiteBlock (b : Block ℕ) (input output : ℕ) : FiniteProgram where
  K := Fin (finiteRegisterBound (program b input output))
  Q := Control b
  program := finitelyNamed (program b input output)

lemma restrictProgram_noChoice (P : Program ℕ Q) (N : ℕ)
    (h : ∀ q,(P.code q).InBounds N) (hi : P.inputStack<N) (ho : P.outputStack<N)
    (hc : NoChoice P) : NoChoice (restrictProgram P N h hi ho) := by
  intro q a b
  cases he : P.code q <;> simp [restrictProgram,he,Instr.restrict]
  · split <;> simp
  · split <;> simp
  · exact False.elim (hc q _ _ he)

lemma restrictProgram_initial (P : Program ℕ Q) (N : ℕ)
    (h : ∀ q,(P.code q).InBounds N) (hi : P.inputStack<N) (ho : P.outputStack<N)
    (word : List Bool) :
    initial (restrictProgram P N h hi ho) word=
      ⟨P.start,restrictStore N (initial P word).stk⟩ := by
  simp only [initial,restrictProgram,restrictStore_update hi]
  rfl

lemma restrictProgram_accepts (P : Program ℕ Q) (N : ℕ)
    (h : ∀ q,(P.code q).InBounds N) (hi : P.inputStack<N) (ho : P.outputStack<N)
    (c : Config ℕ Q) (hc : accepts P c) :
    accepts (restrictProgram P N h hi ho) ⟨c.pc,restrictStore N c.stk⟩ := by
  change (P.code c.pc).restrict N=.halt true
  change P.code c.pc=.halt true at hc
  simp [hc,Instr.restrict]

lemma finitelyNamed_outputs (P : Program ℕ Q) {word out : List Bool} {T : ℕ}
    (h : OutputsIn P word out T) : OutputsIn (finitelyNamed P) word out T := by
  obtain ⟨n,hn,c,hr,ha,ho⟩ := h
  refine ⟨n,hn,⟨c.pc,restrictStore (finiteRegisterBound P) c.stk⟩,?_,?_,?_⟩
  · rw [show initial (finitelyNamed P) word=
      ⟨P.start,restrictStore (finiteRegisterBound P) (initial P word).stk⟩ from
      restrictProgram_initial P _ _ _ _ word]
    exact finitelyNamed_run P hr
  · exact restrictProgram_accepts P _ _ _ _ c ha
  · exact ho

lemma finiteBlock_run (b : Block ℕ) (input output : ℕ) {s t : Store ℕ} {n : ℕ}
    (h : Exec b s t n) :
    Run (finiteBlock b input output).program n
      ⟨entry b,restrictStore (finiteRegisterBound (program b input output)) s⟩
      ⟨finish b,restrictStore (finiteRegisterBound (program b input output)) t⟩ :=
  finitelyNamed_run _ (h.compiles input output)

end Structured
end BalancedAssortments.NPStack
