import BalancedAssortments.CookLevinRawFormulaBound

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

def literalBudget (M : Machine) (n T : ℕ) : ℕ :=
  clauseBudget M n T*clauseWidthBudget M (n+2*T+1)
def catalogueBudget (M : Machine) (n T : ℕ) : ℕ :=
  let A := literalBudget M n T
  let C := clauseBudget M n T
  let B := labelWidth (sourceBound M n T)
  32*(A+1)^2*(B+1)+2*A+C+4
def outputMeasureBudget (M : Machine) (n T : ℕ) : ℕ :=
  (labelWidth (sourceBound M n T)+3)*(2*literalBudget M n T)+3*clauseBudget M n T+4

def constructorBudget (M : Machine) (n T : ℕ) : ℕ :=
  let N := sourceBound M n T
  1024*(N+1)^2+(formulaProfile N N).cost+catalogueBudget M n T+32

def bitConstructorBudget (M : Machine) (n T : ℕ) : ℕ :=
  constructorBudget M n T+32*(outputMeasureBudget M n T+1)+4

lemma builtFormula_counts (M : Machine) (word : List Bool) (clock : List Unit) :
    (builtFormula M word clock).1.length≤clauseBudget M word.length clock.length ∧
    Encoding.bitLiteralCount (builtFormula M word clock).1≤literalBudget M word.length clock.length := by
  have hh := builtFormula_refines M word clock
  have hc := congrArg List.length hh
  have hl := congrArg literalCount hh
  simp only [decodeFormula,List.length_map] at hc
  simp only [decodeFormula,Encoding.decode_literalCount] at hl
  rw [hc,hl]
  exact ⟨tableau_clause_count M word clock.length,tableau_literal_count M word clock.length⟩

lemma builtCatalogue_cost (M : Machine) (word : List Bool) (clock : List Unit) :
    (Encoding.catalogueBits (builtFormula M word clock).1).2≤catalogueBudget M word.length clock.length := by
  have hw := (builtFormula_analysis M word clock).2
  have hh := Encoding.catalogueBits_cost hw
  have hc := builtFormula_counts M word clock
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hc.2 1) 2
  have hmul := Nat.mul_le_mul_right (labelWidth (sourceBound M word.length clock.length)+1)
    (Nat.mul_le_mul_left 32 hsq)
  dsimp only [catalogueBudget]
  omega

lemma builtCatalogue_measure (M : Machine) (word : List Bool) (clock : List Unit) :
    Encoding.rawMeasure (Encoding.catalogueBits (builtFormula M word clock).1).1≤outputMeasureBudget M word.length clock.length := by
  have hh := Encoding.catalogueBits_measure (builtFormula_analysis M word clock).2
  have hc := builtFormula_counts M word clock
  have hp := Nat.mul_le_mul_left (labelWidth (sourceBound M word.length clock.length)+3) (Nat.mul_le_mul_left 2 hc.2)
  unfold outputMeasureBudget
  omega

lemma rawWindowFuel_cost (word : List Bool) (clock : List Unit) :
    (rawWindowFuel word clock).2≤9*word.length+3*clock.length+9 := by
  have hh := rawMap_cost (fun _ : Bool => ((),2)) word 2 (by simp)
  simp only [rawWindowFuel,rawMap_eq,List.length_map]
  omega
lemma rawInputCells_cost (word : List Bool) (clock : List Unit) :
    (rawInputCells word clock).2≤10*clock.length+9*word.length+10 := by
  have hb := rawMap_cost (fun _ : Unit => ([false,true],3)) clock 3 (by simp)
  have hi := rawMap_cost (fun b : Bool => (if b then [true] else [],3)) word 3 (by simp)
  simp only [rawInputCells,rawMap_eq,List.length_map]
  omega

def preludeCost (word : List Bool) (clock : List Unit) : ℕ :=
  (FPTASCostSeeds.countBits clock).2+(rawWindowFuel word clock).2+
    (FPTASCostSeeds.countBits (rawWindowFuel word clock).1).2+
    (enumerateBits (()::clock)).2+(enumerateBits clock).2+
    (enumerateBits (rawWindowFuel word clock).1).2+(rawInputCells word clock).2

lemma preludeCost_bound (M : Machine) (word : List Bool) (clock : List Unit) :
    preludeCost word clock≤1024*(sourceBound M word.length clock.length+1)^2 := by
  let N := sourceBound M word.length clock.length
  have hn : word.length≤N := by unfold N sourceBound;omega
  have ht : clock.length+2≤N := sourceBound_clock M word clock
  have hw : (rawWindowFuel word clock).1.length+2≤N := by rw [rawWindowFuel_length];exact sourceBound_window M word clock
  have c1 := FPTASCostSeeds.countBits_cost clock
  have c2 := rawWindowFuel_cost word clock
  have c3 := FPTASCostSeeds.countBits_cost (rawWindowFuel word clock).1
  have c4 := enumerateBits_cost (()::clock)
  have c5 := enumerateBits_cost clock
  have c6 := enumerateBits_cost (rawWindowFuel word clock).1
  have c7 := rawInputCells_cost word clock
  simp only [List.length_cons] at c4
  have s1 := Nat.pow_le_pow_left (show clock.length+1≤N+1 by omega) 2
  have s3 := Nat.pow_le_pow_left (show (rawWindowFuel word clock).1.length+1≤N+1 by omega) 2
  have s4 := Nat.mul_le_mul (show clock.length+1≤N+1 by omega)
    (show 16*(clock.length+1)+5≤16*(N+1)+5 by omega)
  have s5 := Nat.mul_le_mul (show clock.length≤N+1 by omega)
    (show 16*clock.length+5≤16*(N+1)+5 by omega)
  have s6 := Nat.mul_le_mul (show (rawWindowFuel word clock).1.length≤N+1 by omega)
    (show 16*(rawWindowFuel word clock).1.length+5≤16*(N+1)+5 by omega)
  unfold preludeCost
  change _≤1024*(N+1)^2
  nlinarith

theorem constructRaw_cost (M : Machine) (word : List Bool) (clock : List Unit) :
    (constructRaw (machineConstants M) word clock).2≤constructorBudget M word.length clock.length := by
  have hp := preludeCost_bound M word clock
  have hf := (builtFormula_analysis M word clock).1.cost_le
  have hc := builtCatalogue_cost M word clock
  change preludeCost word clock+(builtFormula M word clock).2+
    (Encoding.catalogueBits (builtFormula M word clock).1).2+32≤_
  dsimp only [constructorBudget]
  omega

theorem constructBits_cost (M : Machine) (word : List Bool) (clock : List Unit) :
    (constructBits (machineConstants M) word clock).2≤bitConstructorBudget M word.length clock.length := by
  have hr := constructRaw_cost M word clock
  have hm := builtCatalogue_measure M word clock
  have he := Encoding.emit_cost (constructRaw (machineConstants M) word clock).1
  change Encoding.rawMeasure (constructRaw (machineConstants M) word clock).1≤_ at hm
  dsimp only [constructBits,bitConstructorBudget]
  omega

end BalancedAssortments.CookLevin
