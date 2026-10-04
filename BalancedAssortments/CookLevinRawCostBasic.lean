import BalancedAssortments.CookLevinClockFuel

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitFormula)

structure DimensionWidths (b : ℕ) (d : RawDimensions) : Prop where
  q : d.q.length≤b
  g : d.g.length≤b
  w : d.w.length≤b
  t : d.t.length≤b
  r : d.r.length≤b

lemma dimensionInputs_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {t p a r : List Bool} (ht : t.length≤b) (hp : p.length≤b) (ha : a.length≤b) (hr : r.length≤b) :
    ∀ i,(d.inputs t p a r i).length≤b := by
  intro i
  rcases hd with ⟨hq,hg,hw,htt,hrh⟩
  fin_cases i <;> simpa [RawDimensions.inputs] using
    (by assumption : _)

def labelWidth (b : ℕ) : ℕ := 32*(b+1)
def labelCost (b : ℕ) : ℕ := 65536*(b+1)^2

lemma indexExpr_width (e : BitExpr 9) (he : e=stateIndexExpr ∨ e=headIndexExpr ∨ e=tapeIndexExpr ∨ e=choiceIndexExpr)
    (b : ℕ) : e.widthPoly.eval b≤labelWidth b := by
  rcases he with rfl|rfl|rfl|rfl <;>
    norm_num [stateIndexExpr,headIndexExpr,tapeIndexExpr,choiceIndexExpr,BitExpr.widthPoly,labelWidth] <;> omega
lemma indexExpr_cost (e : BitExpr 9) (he : e=stateIndexExpr ∨ e=headIndexExpr ∨ e=tapeIndexExpr ∨ e=choiceIndexExpr)
    (b : ℕ) : e.costPoly.eval b≤labelCost b := by
  rcases he with rfl|rfl|rfl|rfl <;>
    norm_num [stateIndexExpr,headIndexExpr,tapeIndexExpr,choiceIndexExpr,BitExpr.widthPoly,BitExpr.costPoly,labelCost] <;> nlinarith

lemma labelExpr_bounds {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    (e : BitExpr 9) (he : e=stateIndexExpr ∨ e=headIndexExpr ∨ e=tapeIndexExpr ∨ e=choiceIndexExpr)
    {t p a r : List Bool} (ht : t.length≤b) (hp : p.length≤b) (ha : a.length≤b) (hr : r.length≤b) :
    (e.run (d.inputs t p a r)).1.length≤labelWidth b ∧ (e.run (d.inputs t p a r)).2≤labelCost b :=
  ⟨(e.run_width _ (dimensionInputs_width hd ht hp ha hr)).trans (indexExpr_width e he b),
    (e.run_cost _ (dimensionInputs_width hd ht hp ha hr)).trans (indexExpr_cost e he b)⟩

lemma stateLabel_bounds {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {t s : List Bool} (ht : t.length≤b) (hs : s.length≤b) :
    (stateLabel d t s).1.length≤labelWidth b ∧ (stateLabel d t s).2≤labelCost b :=
  labelExpr_bounds hd _ (Or.inl rfl) ht (Nat.zero_le _) hs (Nat.zero_le _)
lemma headLabel_bounds {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {t p : List Bool} (ht : t.length≤b) (hp : p.length≤b) :
    (headLabel d t p).1.length≤labelWidth b ∧ (headLabel d t p).2≤labelCost b :=
  labelExpr_bounds hd _ (Or.inr (Or.inl rfl)) ht hp (Nat.zero_le _) (Nat.zero_le _)
lemma tapeLabel_bounds {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {t p a : List Bool} (ht : t.length≤b) (hp : p.length≤b) (ha : a.length≤b) :
    (tapeLabel d t p a).1.length≤labelWidth b ∧ (tapeLabel d t p a).2≤labelCost b :=
  labelExpr_bounds hd _ (Or.inr (Or.inr (Or.inl rfl))) ht hp ha (Nat.zero_le _)
lemma choiceLabel_bounds {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {t r : List Bool} (ht : t.length≤b) (hr : r.length≤b) :
    (choiceLabel d t r).1.length≤labelWidth b ∧ (choiceLabel d t r).2≤labelCost b :=
  labelExpr_bounds hd _ (Or.inr (Or.inr (Or.inr rfl))) ht (Nat.zero_le _) (Nat.zero_le _) hr

structure CodeBound (L C : ℕ) (output : BitFormula × ℕ) : Prop where
  length_le : output.1.length≤L
  cost_le : output.2≤C
lemma CodeBound.mono {L C L' C' : ℕ} {f : BitFormula × ℕ} (h : CodeBound L C f)
    (hl : L≤L') (hc : C≤C') : CodeBound L' C' f := ⟨h.length_le.trans hl,h.cost_le.trans hc⟩
lemma bound_append {L C K D : ℕ} {F G : BitFormula × ℕ} (hF : CodeBound L C F) (hG : CodeBound K D G) :
    CodeBound (L+K) (C+D+L+4) (rawAppend F G) := by
  constructor
  · simpa [rawAppend] using Nat.add_le_add hF.length_le hG.length_le
  · have := hF.cost_le; have := hG.cost_le; have := hF.length_le; simp only [rawAppend]; omega
lemma bound_flatMap {α : Type*} {N L C : ℕ} (xs : List α) (f : α → BitFormula × ℕ)
    (hn : xs.length≤N) (h : ∀ x∈xs,CodeBound L C (f x)) :
    CodeBound (N*L) (N*(C+L+4)+1) (rawFlatMap f xs) := by
  constructor
  · rw [rawFlatMap_eq]
    exact (length_flatMap_le xs _ L (fun x hx => (h x hx).length_le)).trans (Nat.mul_le_mul_right L hn)
  · exact (rawFlatMap_cost f xs C L (fun x hx => (h x hx).cost_le) (fun x hx => (h x hx).length_le)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
lemma bound_force {C : ℕ} {label : List Bool × ℕ} (h : label.2≤C) :
    CodeBound 1 (C+6) (rawForce label) := ⟨by rfl,by simpa [rawForce] using Nat.add_le_add_right h 6⟩
lemma bound_copy {C : ℕ} {a b : List Bool × ℕ} (ha : a.2≤C) (hb : b.2≤C) :
    CodeBound 1 (2*C+8) (rawCopy a b) := by constructor; rfl; simp only [rawCopy];omega
lemma bound_guard {C L D : ℕ} (sign : Bool) {label : List Bool × ℕ} {body : BitFormula × ℕ}
    (hl : label.2≤C) (hb : CodeBound L D body) :
    CodeBound L (C+D+8*L+5) (rawGuardComputed sign label body) := by
  constructor
  · simpa [rawGuardComputed,rawGuard_length] using hb.length_le
  · have hh := rawGuard_cost ⟨label.1,sign⟩ body.1
    have := hb.length_le;have := hb.cost_le
    simp only [rawGuardComputed]
    omega

def familyLength (N : ℕ) : ℕ := 1+N*N
def familyCost (N b : ℕ) : ℕ :=
  N*(labelCost b+4)+1+N*(N*(16*labelWidth b+17)+6)+6*N+10
lemma bound_family {N b : ℕ} (xs : List (List Bool)) (f : List Bool → List Bool × ℕ)
    (hn : xs.length≤N) (hf : ∀ x∈xs,(f x).1.length≤labelWidth b ∧ (f x).2≤labelCost b) :
    CodeBound (familyLength N) (familyCost N b)
      (let labels := rawMap f xs; let clauses := rawExactlyOne labels.1; (clauses.1,labels.2+clauses.2+4)) := by
  have hl : (rawMap f xs).1.length=xs.length := by simp [rawMap_eq]
  have hw : ∀ x∈(rawMap f xs).1,x.length≤labelWidth b := by
    rw [rawMap_eq]
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact (hf a ha).1
  have hm := rawMap_cost f xs (labelCost b) (fun x hx => (hf x hx).2)
  have he := rawExactlyOne_cost hw
  rw [hl] at he
  constructor
  · have hh := rawExactlyOne_length (rawMap f xs).1
    rw [hl] at hh
    exact hh.trans (Nat.add_le_add_left (Nat.mul_self_le_mul_self hn) 1)
  · dsimp only
    unfold familyCost
    have h1 := Nat.mul_le_mul_right (labelCost b+4) hn
    have h2 := Nat.mul_le_mul hn (Nat.add_le_add_right (Nat.mul_le_mul_right (16*labelWidth b+17) hn) 6)
    omega

end BalancedAssortments.CookLevin
