import BalancedAssortments.CookLevinStackClockProgram
import BalancedAssortments.CookLevinStackIndices

/-! Genuine operational materialization of the polynomially many tape/time/
variable-loop tokens used by the bounded tableau constructor. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackFuels
open NPCNF NPMachine NPStack NPStack.Structured
open StackClock (Fresh)

def natural (k : ℕ) : FuelExpr := .constant (List.replicate k ())
def rows (e : FuelExpr) : FuelExpr := .add e (natural 1)
def window (e : FuelExpr) : FuelExpr := .add (.add .input (.mul (natural 2) e)) (natural 1)
def variableFuel (M : Machine) (e : FuelExpr) : FuelExpr :=
  .add (.add (.mul (rows e) (natural (M.stateExtra+1))) (.mul (rows e) (window e)))
    (.add (.mul (rows e) (.mul (window e) (natural (M.symbolExtra+3)))) (.mul e (natural (M.rules.length+1))))

lemma natural_value (k n : ℕ) : (natural k).polynomial.eval n=k := by simp [natural,FuelExpr.polynomial]
lemma rows_value (e : FuelExpr) (n : ℕ) : (rows e).polynomial.eval n=e.polynomial.eval n+1 := by simp [rows,FuelExpr.polynomial,natural_value]
lemma window_value (e : FuelExpr) (n : ℕ) : (window e).polynomial.eval n=n+2*e.polynomial.eval n+1 := by simp [window,FuelExpr.polynomial,natural_value]
lemma variables_value (M : Machine) (e : FuelExpr) (n : ℕ) :
    (variableFuel M e).polynomial.eval n=
      variableCount (M.stateExtra+1) (M.symbolExtra+3) (n+2*e.polynomial.eval n+1) (e.polynomial.eval n) (M.rules.length+1) := by
  simp [variableFuel,FuelExpr.polynomial,rows_value,window_value,natural_value,variableCount]

def materialize (work target : ℕ) (e : FuelExpr) : Block ℕ :=
  .seq (StackClock.compile work e)
    (.seq (.atom (copyAtom work (work+1) target)) (clearStack work))
noncomputable def materializeTime (e : FuelExpr) : Polynomial ℕ :=
  StackClock.timePolynomial e+8*e.polynomial+5

lemma materialize_exec (work target : ℕ) (e : FuelExpr) (s : Store ℕ)
    (hw : 0<work) (ht : target<work) (hf : Fresh s work (StackClock.slots e)) (ho : s target=[]) :
    Exec (materialize work target e) s
      (Function.update s target (List.replicate (e.polynomial.eval (s 0).length) false))
      ((materializeTime e).eval (s 0).length) := by
  have hslots := StackClock.slots_lower e
  have h0 : s work=[] := hf work (by omega) (by omega)
  have h1 : s (work+1)=[] := hf (work+1) (by omega) (by omega)
  have ha := StackClock.compile_exec e work s hw hf
  let bits := List.replicate (e.polynomial.eval (s 0).length) false
  let u := Function.update s work bits
  have hu0 : u work=bits := by simp [u]
  have hu1 : u (work+1)=[] := by simp [u,h1]
  have hut : u target=[] := by simp [u,Function.update,show target≠work by omega,ho]
  have hi : Function.Injective (Macros.copyMap work (work+1) target) := by
    intro i j he;cases i <;> cases j <;> simp only [Macros.copyMap] at he <;> first | rfl | omega
  have hb := copyAtom_run work (work+1) target hi u hu1
  rw [hu0,hut,List.append_nil] at hb
  let v := Function.update u target bits
  have hv0 : v work=bits := by simp [v,Function.update,show work≠target by omega,hu0]
  have hc := clearStack_exec work v
  rw [hv0] at hc
  have he : Function.update v work []=Function.update s target bits :=
    StackClock.clear_accumulate s work target bits bits (by omega) h0
  rw [he] at hc
  have hh := Exec.seq ha (Exec.seq hb hc)
  convert hh using 1 <;> simp only [materializeTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,bits,List.length_replicate] <;> omega

def batch (work : ℕ) : List (ℕ × FuelExpr) → Block ℕ
  | [] => .skip
  | p::ps => .seq (materialize work p.1 p.2) (batch work ps)
def batchSlots : List (ℕ × FuelExpr) → ℕ
  | [] => 3
  | p::ps => max (StackClock.slots p.2) (batchSlots ps)
noncomputable def batchTime : List (ℕ × FuelExpr) → Polynomial ℕ
  | [] => 1
  | p::ps => materializeTime p.2+batchTime ps+1

def batchBindings (ps : List (ℕ × FuelExpr)) (n : ℕ) : List (ℕ × List Bool) :=
  ps.map (fun p => (p.1,List.replicate (p.2.polynomial.eval n) false))

lemma batch_exec (work : ℕ) (ps : List (ℕ × FuelExpr)) (s : Store ℕ)
    (hw : 0<work) (hkeys : (ps.map Prod.fst).Nodup)
    (hbelow : ∀ p∈ps,0<p.1 ∧ p.1<work) (hz : ∀ p∈ps,s p.1=[])
    (hf : Fresh s work (batchSlots ps)) :
    Exec (batch work ps) s (Macros.writes s (batchBindings ps (s 0).length))
      ((batchTime ps).eval (s 0).length) := by
  induction ps generalizing s with
  | nil => simpa [batch,Macros.writes,batchBindings,batchTime] using Exec.skip s
  | cons p ps ih =>
    have hnodup := List.nodup_cons.mp hkeys
    have hp := hbelow p (by simp)
    have hzp := hz p (by simp)
    have hhead : Fresh s work (StackClock.slots p.2) := hf.subrange (by omega) (by simp only [batchSlots];omega)
    have ha := materialize_exec work p.1 p.2 s hw hp.2 hhead hzp
    let bits := List.replicate (p.2.polynomial.eval (s 0).length) false
    let u := Function.update s p.1 bits
    have hu0 : u 0=s 0 := by simp [u,Function.update,show 0≠p.1 by omega]
    have huz : ∀ q∈ps,u q.1=[] := by
      intro q hq
      have hne : q.1≠p.1 := by
        intro he
        exact hnodup.1 (List.mem_map.mpr ⟨q,hq,he⟩)
      simpa [u,Function.update,hne] using hz q (by simp [hq])
    have htail : Fresh u work (batchSlots ps) :=
      (hf.subrange (by omega) (by simp only [batchSlots];omega)).update_outside (Or.inl hp.2) _
    have hb := ih u hnodup.2 (fun q hq => hbelow q (by simp [hq])) huz htail
    rw [hu0] at hb
    have hh := Exec.seq ha hb
    simpa only [batch,batchTime,Polynomial.eval_add,Polynomial.eval_one,batchBindings,List.map_cons,Macros.writes] using hh

def tableauFuels (M : Machine) (e : FuelExpr) : List (ℕ × FuelExpr) :=
  [(11,e),(12,rows e),(13,window e),(14,variableFuel M e),(15,.input)]

end BalancedAssortments.CookLevin.StackFuels
