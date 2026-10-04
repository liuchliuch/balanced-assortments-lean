import BalancedAssortments.CookLevinStackBuilder

noncomputable section
namespace BalancedAssortments.CookLevin.StackBuilder
open NPCNF NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackIndices (inputView)

/-- Proof-side loop state. The actual program realizes each update with the
previously compiled copy, clear, binary increment and emission instructions. -/
def loopState {n : ℕ} (s : Store ℕ) (index : Fin n) (privateBase out : ℕ)
    (bits rest acc : List Bool) : Store ℕ :=
  Function.update (Function.update (Function.update (Function.update s privateBase rest)
    (privateBase+2) (s index.val)) index.val bits) out acc

lemma loopState_out {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ) (bits rest acc : List Bool) :
    loopState s index p out bits rest acc out=acc := by simp [loopState]
lemma loopState_index {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ) (bits rest acc : List Bool)
    (ho : n≤out) : loopState s index p out bits rest acc index.val=bits := by
  have hi : index.val≠out := by have := index.isLt;omega
  simp [loopState,Function.update,hi]
lemma loopState_counter {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ) (bits rest acc : List Bool)
    (ho : n≤out) (hp : out<p) : loopState s index p out bits rest acc p=rest := by
  have hi := index.isLt
  simp [loopState,Function.update,show p≠out by omega,show p≠index.val by omega]
lemma loopState_saved {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ) (bits rest acc : List Bool)
    (ho : n≤out) (hp : out<p) : loopState s index p out bits rest acc (p+2)=s index.val := by
  have hi := index.isLt
  simp [loopState,Function.update,show p+2≠out by omega,show p+2≠index.val by omega]
lemma loopState_scratch {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ) (bits rest acc : List Bool)
    (ho : n≤out) (hp : out<p) : loopState s index p out bits rest acc (p+1)=s (p+1) := by
  have hi := index.isLt
  simp [loopState,Function.update,show p+1≠out by omega,show p+1≠index.val by omega]

lemma loopState_update_out {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ)
    (bits rest acc acc' : List Bool) :
    Function.update (loopState s index p out bits rest acc) out acc'=loopState s index p out bits rest acc' := by
  simp [loopState]
lemma loopState_update_index {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ)
    (bits bits' rest acc : List Bool) (ho : n≤out) :
    Function.update (loopState s index p out bits rest acc) index.val bits'=loopState s index p out bits' rest acc := by
  have hio : index.val≠out := by have := index.isLt;omega
  funext k
  by_cases hk : k=index.val
  · subst k;simp [loopState,Function.update,hio]
  · simp [loopState,Function.update,hk]
lemma loopState_update_counter {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ)
    (bits rest rest' acc : List Bool) (ho : n≤out) (hp : out<p) :
    Function.update (loopState s index p out bits rest acc) p rest'=loopState s index p out bits rest' acc := by
  have hi := index.isLt
  funext k
  by_cases hk : k=p
  · subst k;simp [loopState,Function.update,show p≠out by omega,show p≠index.val by omega]
  · simp [loopState,Function.update,hk]

lemma loopState_low {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ)
    (bits rest acc : List Bool) (k : ℕ) (hk : k<p) (hki : k≠index.val) (hko : k≠out) :
    loopState s index p out bits rest acc k=s k := by
  simp [loopState,Function.update,hki,hko,show k≠p by omega,show k≠p+2 by omega]
lemma loopState_high {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ)
    (bits rest acc : List Bool) (ho : n≤out) (hp : out<p) (k : ℕ) (hk : p+3≤k) :
    loopState s index p out bits rest acc k=s k := by
  have hi := index.isLt
  simp [loopState,Function.update,show k≠out by omega,show k≠index.val by omega,
    show k≠p+2 by omega,show k≠p by omega]
lemma loopState_fresh {n : ℕ} (s : Store ℕ) (index : Fin n) (p out work count : ℕ)
    (bits rest acc : List Bool) (ho : n≤out) (hp : out<p) (hw : p+3≤work)
    (hf : Fresh s work count) : Fresh (loopState s index p out bits rest acc) work count := by
  intro k hkl hkr
  rw [loopState_high s index p out bits rest acc ho hp k (by omega)]
  exact hf k hkl hkr

lemma loopState_view {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ)
    (bits rest acc : List Bool) (ho : n≤out) (hp : out<p) :
    inputView n (loopState s index p out bits rest acc)=Function.update (inputView n s) index bits := by
  funext j
  by_cases hj : j=index
  · subst j;simpa [inputView] using loopState_index s index p out bits rest acc ho
  · have hv : j.val≠index.val := fun h => hj (Fin.ext h)
    have hjo : j.val≠out := by have := j.isLt;omega
    simpa [inputView,Function.update,hj] using loopState_low s index p out bits rest acc j.val
      (by have := j.isLt;omega) hv hjo

end BalancedAssortments.CookLevin.StackBuilder
