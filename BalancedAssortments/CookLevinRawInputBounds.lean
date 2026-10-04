import BalancedAssortments.CookLevinRawWidthsSteps

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

 def sourceBound (M : Machine) (n T : ℕ) : ℕ :=
  n+2*T+M.stateExtra+M.symbolExtra+M.rules.length+20

lemma sourceBound_window (M : Machine) (word : List Bool) (clock : List Unit) :
    windowWidth word clock.length+2≤sourceBound M word.length clock.length := by
  unfold sourceBound windowWidth;omega
lemma sourceBound_clock (M : Machine) (word : List Bool) (clock : List Unit) :
    clock.length+2≤sourceBound M word.length clock.length := by unfold sourceBound;omega

lemma range_bits_width (n b : ℕ) (h : n≤b) : ListWidths b ((List.range n).map Nat.bits) := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  exact (bits_length_le_self i).trans ((Nat.le_of_lt (List.mem_range.mp hi)).trans h)

structure ConstantsBound (N b : ℕ) (c : MachineConstants) : Prop where
  states_length : c.states.length≤N
  symbols_length : c.symbols.length≤N
  choices_length : c.choices.length≤N
  accepting_length : c.accepting.length≤N
  rules_length : c.rules.length≤N
  states_width : ListWidths b c.states
  symbols_width : ListWidths b c.symbols
  choices_width : ListWidths b c.choices
  accepting_width : ListWidths b c.accepting
  rules_width : ∀ r∈c.rules,RuleWidths b r
  start_width : c.start.length≤b
  q_width : c.q.length≤b
  g_width : c.g.length≤b
  r_width : c.r.length≤b

lemma machineConstants_bound (M : Machine) (n T : ℕ) :
    ConstantsBound (sourceBound M n T) (sourceBound M n T) (machineConstants M) := by
  have hq : M.stateExtra+1≤sourceBound M n T := by unfold sourceBound;omega
  have hg : M.symbolExtra+3≤sourceBound M n T := by unfold sourceBound;omega
  have hr : M.rules.length+1≤sourceBound M n T := by unfold sourceBound;omega
  constructor
  · simpa [machineConstants] using hq
  · simpa [machineConstants] using hg
  · simpa [machineConstants] using hr
  · change (((List.finRange (M.stateExtra+1)).filter M.accepting).map (fun s => s.val.bits)).length≤_
    simp only [List.length_map]
    exact ((List.length_filter_le _ _).trans_eq List.length_finRange).trans hq
  · change (M.rules.map _).length≤_
    simpa only [List.length_map] using (Nat.le_succ M.rules.length).trans hr
  · exact range_bits_width _ _ hq
  · exact range_bits_width _ _ hg
  · exact range_bits_width _ _ hr
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact (bits_length_le_self i.val).trans (i.isLt.le.trans hq)
  · intro r hrr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hrr
    constructor
    · exact (bits_length_le_self r.source.val).trans (r.source.isLt.le.trans hq)
    · exact (bits_length_le_self r.target.val).trans (r.target.isLt.le.trans hq)
    · exact (bits_length_le_self r.read.val).trans (r.read.isLt.le.trans hg)
    · exact (bits_length_le_self r.write.val).trans (r.write.isLt.le.trans hg)
  · exact (bits_length_le_self M.start.val).trans (M.start.isLt.le.trans hq)
  · exact (bits_length_le_self _).trans hq
  · exact (bits_length_le_self _).trans hg
  · exact (bits_length_le_self _).trans hr

lemma builtDimensions_width (M : Machine) (word : List Bool) (clock : List Unit) :
    DimensionWidths (sourceBound M word.length clock.length) (builtDimensions M word clock) := by
  have hc := machineConstants_bound M word.length clock.length
  constructor
  · exact hc.q_width
  · exact hc.g_width
  · have hh := FPTASCostSeeds.countBits_width (rawWindowFuel word clock).1
    rw [rawWindowFuel_length] at hh
    exact hh.trans ((Nat.le_succ _).trans (sourceBound_window M word clock))
  · exact (FPTASCostSeeds.countBits_width clock).trans ((Nat.le_succ _).trans (sourceBound_clock M word clock))
  · exact hc.r_width

lemma enumerateBits_width {b : ℕ} (fuel : List Unit) (h : fuel.length≤b) :
    ListWidths b (enumerateBits fuel).1 := by
  intro x hx
  have hh := enumerateFrom_width [] fuel x hx
  simp only [List.length_nil,Nat.zero_add] at hh
  exact hh.trans h

lemma rawInputCells_width (word : List Bool) (clock : List Unit) :
    ListWidths 2 (rawInputCells word clock).1 := by
  intro x hx
  simp only [rawInputCells,rawMap_eq,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with ((⟨u,hu,rfl⟩ | ⟨b,hb,rfl⟩) | ⟨u,hu,rfl⟩) | rfl
  · decide
  · split <;> decide
  · decide
  · decide

end BalancedAssortments.CookLevin
