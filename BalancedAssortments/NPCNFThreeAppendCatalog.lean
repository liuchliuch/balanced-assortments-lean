import BalancedAssortments.NPCNFThreeCatalogued

/-! Catalogue-preserving variant of the same OR-chain reduction. This permits
streaming bytecode to emit each newly allocated variable once, avoiding a second
occurrence deduplication pass. Original sparse labels remain unchanged. -/
namespace BalancedAssortments.NPCNF

def labelsSatisfy (P : ℕ → Prop) (F : Formula) : Prop := ∀ c∈F,∀ l∈c,P l.var

lemma gate_labels {P : ℕ → Prop} {a b : Literal} {z : ℕ}
    (ha : P a.var) (hb : P b.var) (hz : P z) : labelsSatisfy P (orGate a b z) := by
  intro c hc l hl
  simp only [orGate,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp only [List.mem_cons,List.mem_nil_iff,or_false] at hl
  · rcases hl with rfl | rfl <;> assumption
  · rcases hl with rfl | rfl <;> assumption
  · rcases hl with rfl | rfl | rfl <;> assumption

lemma chain_labels {P : ℕ → Prop} (next : ℕ) (a : Literal) (rest : Clause)
    (ha : P a.var) (hr : ∀ l∈rest,P l.var) (hfresh : ∀ z,next≤z → P z) :
    labelsSatisfy P (chain next a rest).1 := by
  induction rest generalizing next a with
  | nil =>
    intro c hc l hl
    simp only [chain,List.mem_singleton] at hc
    subst c
    simp only [List.mem_singleton] at hl
    subst l
    exact ha
  | cons b bs ih =>
    have hg := gate_labels ha (hr b (by simp)) (hfresh next le_rfl)
    have ht := ih (next+1) (positive next) (hfresh next le_rfl)
      (fun l hl => hr l (by simp [hl])) (fun z hz => hfresh z (by omega))
    intro c hc l hl
    simp only [chain,List.mem_append] at hc
    rcases hc with hc | hc
    · exact hg c hc l hl
    · exact ht c hc l hl

lemma clause_labels {P : ℕ → Prop} (next : ℕ) (c : Clause)
    (hc : ∀ l∈c,P l.var) (hfresh : ∀ z,next≤z → P z) :
    labelsSatisfy P (clauseToThree next c).1 := by
  cases c with
  | nil => intro d hd l hl; simp [clauseToThree] at hd; subst d;simp at hl
  | cons a as => exact chain_labels next a as (hc a (by simp)) (fun l hl=>hc l (by simp [hl])) hfresh

lemma toThree_labels {P : ℕ → Prop} (next : ℕ) (F : Formula)
    (h : labelsSatisfy P F) (hfresh : ∀ z,next≤z → P z) :
    labelsSatisfy P (toThree next F).1 := by
  induction F generalizing next with
  | nil => intro c hc;simp [toThree] at hc
  | cons c cs ih =>
    have hh := clause_labels next c (h c (by simp)) hfresh
    have ht := ih (clauseToThree next c).2 (fun d hd=>h d (by simp [hd]))
      (fun z hz=>hfresh z (by simp only [clauseToThree_next] at hz;omega))
    intro d hd l hl
    simp only [toThree,List.mem_append] at hd
    rcases hd with hd | hd
    · exact hh d hd l hl
    · exact ht d hd l hl

def allocatedLabels (next count : ℕ) : List ℕ := (List.range count).map (next+·)

def reduceAppendCatalog (input : Catalogued) : Catalogued :=
  ⟨input.catalog++allocatedLabels (freshStart input) (freshCount input.formula),
    (toThree (freshStart input) input.formula).1⟩

lemma allocated_mem (next count z : ℕ) : z∈allocatedLabels next count ↔ next≤z ∧ z<next+count := by
  simp only [allocatedLabels,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩;omega
  · rintro ⟨hlo,hhi⟩;exact ⟨z-next,by omega,by omega⟩

lemma allocated_nodup (next count : ℕ) : (allocatedLabels next count).Nodup := by
  apply (List.nodup_map_iff (show Function.Injective (next+·) from by intro a b h;dsimp only at h;omega)).2
  exact List.nodup_range

theorem reduceAppendCatalog_valid (input : Catalogued) (h : input.Valid) : (reduceAppendCatalog input).Valid := by
  constructor
  · apply List.nodup_append.mpr
    refine ⟨h.1,allocated_nodup _ _,?_⟩
    intro a ha b hb he
    have hlo := ((allocated_mem _ _ b).1 hb).1
    have hmax := label_le_max ha
    unfold freshStart at hlo
    omega
  · intro c hc l hl
    have horigin := toThree_labels (P := fun z=>z∈input.catalog ∨ freshStart input≤z)
      (freshStart input) input.formula (fun c hc l hl=>Or.inl (h.2 c hc l hl)) (fun z hz=>Or.inr hz)
    have hbound := toThree_bounded (freshStart_bounds h) c hc l hl
    rw [toThree_next] at hbound
    change l.var∈input.catalog++allocatedLabels (freshStart input) (freshCount input.formula)
    rcases horigin c hc l hl with ho | ho
    · exact List.mem_append_left _ ho
    · exact List.mem_append_right _ ((allocated_mem _ _ _).2 ⟨ho,hbound⟩)

theorem reduceAppendCatalog_sat_iff (input : Catalogued) (h : input.Valid) :
    (reduceAppendCatalog input).Sat ↔ input.Sat := toThree_sat_iff (freshStart_bounds h)

theorem reduceAppendCatalog_three (input : Catalogued) : ThreeCNF (reduceAppendCatalog input).formula :=
  toThree_three _ _

end BalancedAssortments.NPCNF
