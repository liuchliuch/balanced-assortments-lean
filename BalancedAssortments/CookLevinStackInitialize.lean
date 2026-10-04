import BalancedAssortments.CookLevinStackFuels
import BalancedAssortments.CookLevinStackCount
import BalancedAssortments.CookLevinPolynomialCost

/-! Exact initialized scalar and read-only fuel registers for the streaming
Cook–Levin builder. The actual initialization code follows in separate modules. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackInitialize
open NPCNF NPMachine NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)

def emptyStore : Store ℕ := fun _ => []
def inputStore (word : List Bool) : Store ℕ := Function.update emptyStore 0 word

def specBindings (M : Machine) (word : List Bool) (T : ℕ) : List (ℕ × List Bool) :=
  let n := word.length
  let W := n+2*T+1
  let V := variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1)
  [(0,(M.stateExtra+1).bits),(1,(M.symbolExtra+3).bits),
    (2,StackCount.counterBits W),(3,StackCount.counterBits T),(4,(M.rules.length+1).bits),
    (7,StackCount.counterBits n),(9,word),(11,List.replicate T false),
    (12,List.replicate (T+1) false),(13,List.replicate W false),(14,List.replicate V false),
    (15,List.replicate n false)]
def specStore (M : Machine) (word : List Bool) (T : ℕ) : Store ℕ :=
  Macros.writes emptyStore (specBindings M word T)
def scalarEnv (M : Machine) (word : List Bool) (T : ℕ) : Fin 9 → List Bool :=
  StackIndices.inputView 9 (specStore M word T)

theorem scalarEnv_eq (M : Machine) (word : List Bool) (T : ℕ) :
    scalarEnv M word T= ![(M.stateExtra+1).bits,(M.symbolExtra+3).bits,
      StackCount.counterBits (word.length+2*T+1),StackCount.counterBits T,(M.rules.length+1).bits,
      [],[],StackCount.counterBits word.length,[]] := by
  funext i
  fin_cases i <;> simp [scalarEnv,StackIndices.inputView,specStore,specBindings,Macros.writes,emptyStore]

@[simp] lemma specStore_word (M : Machine) (word : List Bool) (T : ℕ) : specStore M word T 9=word := by
  simp [specStore,specBindings,Macros.writes]
@[simp] lemma specStore_output (M : Machine) (word : List Bool) (T : ℕ) : specStore M word T 10=[] := by
  simp [specStore,specBindings,Macros.writes,emptyStore]
@[simp] lemma specStore_clock (M : Machine) (word : List Bool) (T : ℕ) : specStore M word T 11=List.replicate T false := by
  simp [specStore,specBindings,Macros.writes]
@[simp] lemma specStore_rows (M : Machine) (word : List Bool) (T : ℕ) : specStore M word T 12=List.replicate (T+1) false := by
  simp [specStore,specBindings,Macros.writes]
@[simp] lemma specStore_window (M : Machine) (word : List Bool) (T : ℕ) : specStore M word T 13=List.replicate (windowWidth word T) false := by
  simp [specStore,specBindings,Macros.writes,windowWidth]
@[simp] lemma specStore_variables (M : Machine) (word : List Bool) (T : ℕ) :
    specStore M word T 14=List.replicate (variableCount (M.stateExtra+1) (M.symbolExtra+3) (windowWidth word T) T (M.rules.length+1)) false := by
  simp [specStore,specBindings,Macros.writes,windowWidth]
@[simp] lemma specStore_length (M : Machine) (word : List Bool) (T : ℕ) : specStore M word T 15=List.replicate word.length false := by
  simp [specStore,specBindings,Macros.writes]

lemma writes_untouched (s : Store ℕ) (bindings : List (ℕ × List Bool)) (k : ℕ)
    (h : ∀ b∈bindings,b.1≠k) : Macros.writes s bindings k=s k := by
  induction bindings generalizing s with
  | nil => rfl
  | cons b bs ih =>
    rw [Macros.writes,ih _ (fun x hx => h x (by simp [hx]))]
    exact Function.update_of_ne (Ne.symm (h b (by simp))) _ _

theorem specStore_high (M : Machine) (word : List Bool) (T k : ℕ) (hk : 16≤k) :
    specStore M word T k=[] := by
  unfold specStore
  rw [writes_untouched]
  · rfl
  · intro b hb
    simp only [specBindings,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only <;> omega

def bound (M : Machine) (n T : ℕ) : ℕ := sourceBound M n T+tableauVariableCount M n T+32

lemma bound_window (M : Machine) (word : List Bool) (T : ℕ) : windowWidth word T+2≤bound M word.length T := by
  unfold bound sourceBound windowWidth
  omega
lemma bound_clock (M : Machine) (word : List Bool) (T : ℕ) : T+2≤bound M word.length T := by
  unfold bound sourceBound
  omega
lemma bound_word (M : Machine) (word : List Bool) (T : ℕ) : word.length+2≤bound M word.length T := by
  unfold bound sourceBound
  omega

lemma specStore_field_width (M : Machine) (word : List Bool) (T : ℕ) :
    ∀ i : Fin 9,(specStore M word T i.val).length≤bound M word.length T := by
  have hq := bits_length_le_self (M.stateExtra+1)
  have hg := bits_length_le_self (M.symbolExtra+3)
  have hr := bits_length_le_self (M.rules.length+1)
  have hw := StackCount.counterBits_width (word.length+2*T+1)
  have ht := StackCount.counterBits_width T
  have hn := StackCount.counterBits_width word.length
  intro i
  change (scalarEnv M word T i).length≤_
  rw [scalarEnv_eq]
  fin_cases i <;> dsimp
  all_goals unfold bound sourceBound;omega

lemma specStore_fuel_width (M : Machine) (word : List Bool) (T : ℕ) :
    ∀ r∈([9,11,12,13,14,15] : List ℕ),(specStore M word T r).length+1≤bound M word.length T := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [specStore_word,specStore_clock,specStore_rows,specStore_window,specStore_variables,specStore_length,List.length_replicate]
  all_goals simp only [bound,sourceBound,tableauVariableCount,windowWidth];omega

lemma bound_polynomial (M : Machine) (p : Polynomial ℕ) :
    NatPolynomial (fun n => bound M n (p.eval n)) := by
  have hs := sourceBound_poly M p
  dsimp only [bound,tableauVariableCount,variableCount]
  close_poly

end BalancedAssortments.CookLevin.StackInitialize
