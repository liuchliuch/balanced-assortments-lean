import BalancedAssortments.CookLevinStackInitializeCounts

noncomputable section
namespace BalancedAssortments.CookLevin.StackInitialize
open NPCNF NPMachine NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)

def constants (M : Machine) : List (ℕ × List Bool) :=
  [(0,(M.stateExtra+1).bits),(1,(M.symbolExtra+3).bits),(4,(M.rules.length+1).bits)]
def counts : List (Fin 9 × ℕ) := [(3,11),(2,13),(7,15)]
def savedStore (word : List Bool) : Store ℕ := Function.update (inputStore word) 9 word
def fuelStore (M : Machine) (e : FuelExpr) (word : List Bool) : Store ℕ :=
  Macros.writes (savedStore word) (StackFuels.batchBindings (StackFuels.tableauFuels M e) word.length)
def preparedStore (M : Machine) (e : FuelExpr) (word : List Bool) : Store ℕ :=
  Macros.writes (fuelStore M e word) (constants M)

def initializeBlock (M : Machine) (e : FuelExpr) : Block ℕ :=
  .seq (.atom (copyAtom 0 101 9))
    (.seq (StackFuels.batch 100 (StackFuels.tableauFuels M e))
      (.seq (setBatch (constants M)) (countBatch counts)))

theorem prepared_high (M : Machine) (e : FuelExpr) (word : List Bool) (k : ℕ) (hk : 16≤k) :
    preparedStore M e word k=[] := by
  simp [preparedStore,constants,fuelStore,StackFuels.batchBindings,StackFuels.tableauFuels,
    savedStore,inputStore,emptyStore,Macros.writes,Function.update,show k≠0 by omega,
    show k≠1 by omega,show k≠4 by omega,show k≠9 by omega,show k≠11 by omega,
    show k≠12 by omega,show k≠13 by omega,show k≠14 by omega,show k≠15 by omega]

lemma prepared_fields (M : Machine) (e : FuelExpr) (word : List Bool) :
    StackIndices.inputView 9 (preparedStore M e word)=
      ![(M.stateExtra+1).bits,(M.symbolExtra+3).bits,[],[],(M.rules.length+1).bits,[],[],[],[]] := by
  funext i;fin_cases i <;>
    simp [StackIndices.inputView,preparedStore,constants,fuelStore,StackFuels.batchBindings,
      StackFuels.tableauFuels,savedStore,inputStore,emptyStore,Macros.writes]

lemma prepared_width (M : Machine) (e : FuelExpr) (word : List Bool) :
    ∀ i : Fin 9,(preparedStore M e word i.val).length≤bound M word.length (e.polynomial.eval word.length) := by
  have hq := bits_length_le_self (M.stateExtra+1)
  have hg := bits_length_le_self (M.symbolExtra+3)
  have hr := bits_length_le_self (M.rules.length+1)
  intro i
  change (StackIndices.inputView 9 (preparedStore M e word) i).length≤_
  rw [prepared_fields]
  fin_cases i <;> dsimp
  all_goals unfold bound sourceBound;omega

lemma prepared_fuels (M : Machine) (e : FuelExpr) (word : List Bool) :
    ∀ b∈counts,9≤b.2 ∧ b.2<20 ∧
      preparedStore M e word b.2=List.replicate (preparedStore M e word b.2).length false := by
  intro b hb
  simp only [counts,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl
  all_goals simp [preparedStore,constants,fuelStore,StackFuels.batchBindings,StackFuels.tableauFuels,Macros.writes]

lemma prepared_fuel_bounds (M : Machine) (e : FuelExpr) (word : List Bool) :
    ∀ b∈counts,(preparedStore M e word b.2).length+1≤bound M word.length (e.polynomial.eval word.length) := by
  intro b hb
  simp only [counts,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl
  all_goals simp only [preparedStore,constants,fuelStore,StackFuels.batchBindings,StackFuels.tableauFuels,
    List.map_cons,List.map_nil,Macros.writes]
  all_goals simp [StackFuels.window_value,FuelExpr.polynomial]
  all_goals unfold bound sourceBound;omega

lemma initialized_eq (M : Machine) (e : FuelExpr) (word : List Bool) :
    Macros.writes (preparedStore M e word) (countBindings (preparedStore M e word) counts)=
      specStore M word (e.polynomial.eval word.length) := by
  funext k
  by_cases hk : k<16
  · interval_cases k <;>
      simp [countBindings,counts,preparedStore,constants,fuelStore,StackFuels.batchBindings,
        StackFuels.tableauFuels,StackFuels.rows_value,StackFuels.window_value,StackFuels.variables_value,
        FuelExpr.polynomial,savedStore,inputStore,emptyStore,Macros.writes,specStore,specBindings]
  · rw [writes_untouched]
    · rw [prepared_high M e word k (by omega),specStore_high M word _ k (by omega)]
    · intro b hb
      simp only [countBindings,counts,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl <;> simp only <;> omega

noncomputable def initializeBudget (M : Machine) (e : FuelExpr) (n : ℕ) : ℕ :=
  (5*n+2)+(StackFuels.batchTime (StackFuels.tableauFuels M e)).eval n+
    (3*n+2*(M.stateExtra+1).bits.length+2*(M.symbolExtra+3).bits.length+2*(M.rules.length+1).bits.length+13)+
    countBatchBudget (bound M n (e.polynomial.eval n)) counts+3

theorem initialize_exec (M : Machine) (e : FuelExpr) (word : List Bool) :
    ∃ t≤ initializeBudget M e word.length,
      Exec (initializeBlock M e) (inputStore word) (specStore M word (e.polynomial.eval word.length)) t := by
  have hcopy := copyAtom_run 0 101 9 (by
    intro i j he;cases i <;> cases j <;> norm_num [Macros.copyMap] at he <;> rfl)
    (inputStore word) (by simp [inputStore,emptyStore])
  simp only [inputStore,Function.update_self] at hcopy
  have hcopy' : Exec (.atom (copyAtom 0 101 9)) (inputStore word) (savedStore word) (5*word.length+2) := by
    simpa [inputStore,emptyStore,savedStore] using hcopy
  have hf := StackFuels.batch_exec 100 (StackFuels.tableauFuels M e) (savedStore word) (by omega)
    (by simp [StackFuels.tableauFuels])
    (by intro p hp;simp only [StackFuels.tableauFuels,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl <;> norm_num)
    (by intro p hp;simp only [StackFuels.tableauFuels,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl <;> simp [savedStore,inputStore,emptyStore])
    (by intro k hk _;simp [savedStore,inputStore,emptyStore,Function.update,show k≠0 by omega,show k≠9 by omega])
  have hs0 : savedStore word 0=word := by simp [savedStore,inputStore]
  rw [hs0] at hf
  have hc := setBatch_exec (fuelStore M e word) (constants M)
  have hcost : setBatchCost (fuelStore M e word) (constants M)=
      3*word.length+2*(M.stateExtra+1).bits.length+2*(M.symbolExtra+3).bits.length+2*(M.rules.length+1).bits.length+13 := by
    simp [setBatchCost,constants,fuelStore,StackFuels.batchBindings,StackFuels.tableauFuels,
      Macros.writes,savedStore,inputStore,emptyStore]
    omega
  rw [hcost] at hc
  obtain ⟨t,ht,hr⟩ := countBatch_exec (preparedStore M e word) counts
    (bound M word.length (e.polynomial.eval word.length))
    (prepared_fuels M e word) (prepared_fuel_bounds M e word) (prepared_width M e word)
    (fun k hk => prepared_high M e word k (by omega))
  rw [initialized_eq] at hr
  refine ⟨_,?_,Exec.seq hcopy' (Exec.seq hf (Exec.seq hc hr))⟩
  unfold initializeBudget
  omega

end BalancedAssortments.CookLevin.StackInitialize
