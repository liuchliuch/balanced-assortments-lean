import BalancedAssortments.NPCNFBasic

/-! Linear Tseitin OR-chain conversion of arbitrary CNF to clauses of length
at most three. Fresh variables are allocated by a counter; no loop enumerates
the numeric magnitude of a source label. Empty and short clauses are preserved
semantically, and repeated literals need no special case. -/
namespace BalancedAssortments.NPCNF

/-- The three clauses express z ↔ (a ∨ b). -/
def orGate (a b : Literal) (z : ℕ) : Formula :=
  [[a.neg,positive z],[b.neg,positive z],[a,b,negative z]]

def chain (next : ℕ) (a : Literal) : Clause → Formula × ℕ
  | [] => ([[a]],next)
  | b::bs =>
      let tail := chain (next+1) (positive next) bs
      (orGate a b next ++ tail.1,tail.2)

def clauseToThree (next : ℕ) : Clause → Formula × ℕ
  | [] => ([[]],next)
  | a::as => chain next a as

def toThree (next : ℕ) : Formula → Formula × ℕ
  | [] => ([],next)
  | c::cs =>
      let head := clauseToThree next c
      let tail := toThree head.2 cs
      (head.1++tail.1,tail.2)

def freshCount (F : Formula) : ℕ := (F.map (fun c => c.length.pred)).sum

@[simp] theorem chain_next (next : ℕ) (a : Literal) (rest : Clause) :
    (chain next a rest).2 = next+rest.length := by
  induction rest generalizing next a with
  | nil => simp [chain]
  | cons b bs ih => simp [chain,ih]; omega

@[simp] theorem clauseToThree_next (next : ℕ) (c : Clause) :
    (clauseToThree next c).2 = next+c.length.pred := by cases c <;> simp [clauseToThree]

@[simp] theorem toThree_next (next : ℕ) (F : Formula) : (toThree next F).2 = next+freshCount F := by
  induction F generalizing next with
  | nil => simp [toThree,freshCount]
  | cons c cs ih => simp [toThree,ih,freshCount]; omega

lemma gate_three (a b : Literal) (z : ℕ) : ThreeCNF (orGate a b z) := by
  simp [ThreeCNF,orGate]

lemma chain_three (next : ℕ) (a : Literal) (rest : Clause) : ThreeCNF (chain next a rest).1 := by
  induction rest generalizing next a with
  | nil => intro c hc; simp only [chain,List.mem_singleton] at hc; subst c; simp
  | cons b bs ih =>
    intro c hc
    simp only [chain,List.mem_append] at hc
    exact hc.elim (gate_three a b next c) (ih (next+1) (positive next) c)

lemma clauseToThree_three (next : ℕ) (c : Clause) : ThreeCNF (clauseToThree next c).1 := by
  cases c with
  | nil => intro c hc; simp only [clauseToThree,List.mem_singleton] at hc; subst c; simp
  | cons a as => exact chain_three next a as

theorem toThree_three (next : ℕ) (F : Formula) : ThreeCNF (toThree next F).1 := by
  induction F generalizing next with
  | nil => intro c hc; simp [toThree] at hc
  | cons c cs ih =>
    intro d hd
    simp only [toThree,List.mem_append] at hd
    exact hd.elim (clauseToThree_three next c d) (ih _ d)

lemma gate_truth (σ : Assignment) (a b : Literal) (z : ℕ) :
    formulaEval σ (orGate a b z) = true ↔ σ z = (literalEval σ a || literalEval σ b) := by
  simp only [orGate,formulaEval_cons,formulaEval_nil,clauseEval_cons,clauseEval_nil,
    literalEval_neg,literalEval_positive,literalEval_negative]
  cases literalEval σ a <;> cases literalEval σ b <;> cases σ z <;> decide

lemma gate_bounded {next : ℕ} {a b : Literal} (ha : a.var < next) (hb : b.var < next) :
    variablesBounded (next+1) (orGate a b next) := by
  simp [variablesBounded,clauseBounded,orGate]
  omega

lemma chain_bounded {next : ℕ} {a : Literal} {rest : Clause}
    (h : clauseBounded next (a::rest)) : variablesBounded (chain next a rest).2 (chain next a rest).1 := by
  induction rest generalizing next a with
  | nil =>
    intro c hc l hl
    simp only [chain,List.mem_singleton] at hc
    subst c
    simp only [List.mem_singleton] at hl
    subst l
    exact h a (by simp)
  | cons b bs ih =>
    have ha := h a (by simp)
    have hb := h b (by simp)
    have hrest : clauseBounded (next+1) (positive next::bs) := by
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · exact (h l (by simp [hl])).trans_le (by omega)
    have ht := ih hrest
    intro c hc
    simp only [chain,List.mem_append] at hc
    rcases hc with hc | hc
    · apply clauseBounded_mono (n := (chain (next+1) (positive next) bs).2) (gate_bounded ha hb c hc)
      simp only [chain_next]; omega
    · exact ht c hc

lemma clauseToThree_bounded {next : ℕ} {c : Clause} (h : clauseBounded next c) :
    variablesBounded (clauseToThree next c).2 (clauseToThree next c).1 := by
  cases c with
  | nil => intro d hd l hl; simp [clauseToThree] at hd; subst d; simp at hl
  | cons a as => exact chain_bounded h

theorem toThree_bounded {next : ℕ} {F : Formula} (h : variablesBounded next F) :
    variablesBounded (toThree next F).2 (toThree next F).1 := by
  induction F generalizing next with
  | nil => intro c hc; simp [toThree] at hc
  | cons c cs ih =>
    have hc := clauseToThree_bounded (h c (by simp))
    have hnext : next ≤ (clauseToThree next c).2 := by simp
    have htail : variablesBounded (clauseToThree next c).2 cs :=
      variablesBounded_mono (fun d hd => h d (by simp [hd])) hnext
    have ht := ih htail
    intro d hd
    simp only [toThree,List.mem_append] at hd
    rcases hd with hd | hd
    · apply clauseBounded_mono (n := (toThree (clauseToThree next c).2 cs).2) (hc d hd)
      rw [toThree_next]
      omega
    · exact ht d hd

/-- Soundness does not require freshness: any assignment satisfying the output
necessarily satisfies the original disjunction. -/
lemma chain_sound (σ : Assignment) (next : ℕ) (a : Literal) (rest : Clause)
    (h : formulaEval σ (chain next a rest).1 = true) : clauseEval σ (a::rest) = true := by
  induction rest generalizing next a with
  | nil => simpa [chain] using h
  | cons b bs ih =>
    have hh : formulaEval σ (orGate a b next) = true ∧
        formulaEval σ (chain (next+1) (positive next) bs).1 = true := by simpa [chain] using h
    have hg := (gate_truth σ a b next).mp hh.1
    have ht := ih (next+1) (positive next) hh.2
    simp only [clauseEval_cons,literalEval_positive,hg] at ht ⊢
    simpa only [Bool.or_assoc] using ht

lemma clauseToThree_sound (σ : Assignment) (next : ℕ) (c : Clause)
    (h : formulaEval σ (clauseToThree next c).1 = true) : clauseEval σ c = true := by
  cases c with
  | nil => simpa [clauseToThree] using h
  | cons a as => exact chain_sound σ next a as h

theorem toThree_sound (σ : Assignment) (next : ℕ) (F : Formula)
    (h : formulaEval σ (toThree next F).1 = true) : formulaEval σ F = true := by
  induction F generalizing next with
  | nil => rfl
  | cons c cs ih =>
    have hh : formulaEval σ (clauseToThree next c).1 = true ∧
        formulaEval σ (toThree (clauseToThree next c).2 cs).1 = true := by simpa [toThree] using h
    simp only [formulaEval_cons,Bool.and_eq_true]
    exact ⟨clauseToThree_sound σ next c hh.1,ih _ hh.2⟩

lemma update_agrees (σ : Assignment) (next : ℕ) (value : Bool) :
    AgreeBelow next σ (Function.update σ next value) := by
  intro v hv
  simp [Function.update,ne_of_lt hv]

/-- Completeness explicitly extends the original certificate on fresh labels. -/
lemma chain_complete (σ : Assignment) {next : ℕ} {a : Literal} {rest : Clause}
    (hb : clauseBounded next (a::rest)) (hs : clauseEval σ (a::rest) = true) :
    ∃ τ : Assignment,AgreeBelow next σ τ ∧ formulaEval τ (chain next a rest).1 = true := by
  induction rest generalizing next a σ with
  | nil =>
    refine ⟨σ,fun _ _ => rfl,?_⟩
    simpa [chain] using hs
  | cons b bs ih =>
    let σ₁ := Function.update σ next (literalEval σ a || literalEval σ b)
    have hagree : AgreeBelow next σ σ₁ := update_agrees σ next _
    have ha := hb a (by simp)
    have hbb := hb b (by simp)
    have hbs : clauseBounded next bs := fun l hl => hb l (by simp [hl])
    have hnew : clauseBounded (next+1) (positive next::bs) := by
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · exact (hbs l hl).trans_le (by omega)
    have hsat : clauseEval σ₁ (positive next::bs) = true := by
      simp only [clauseEval_cons,literalEval_positive]
      rw [show σ₁ next = (literalEval σ a || literalEval σ b) by simp [σ₁],
        ← clauseEval_congr hagree hbs]
      simpa only [clauseEval_cons,Bool.or_assoc] using hs
    obtain ⟨τ,ht,hsatτ⟩ := ih σ₁ hnew hsat
    have hgate : formulaEval σ₁ (orGate a b next) = true := by
      apply (gate_truth σ₁ a b next).mpr
      rw [← literalEval_congr hagree ha,← literalEval_congr hagree hbb]
      simp [σ₁]
    have hgateτ : formulaEval τ (orGate a b next) = true := by
      rw [← formulaEval_congr ht (gate_bounded ha hbb)]
      exact hgate
    refine ⟨τ,?_,?_⟩
    · intro v hv
      exact (hagree v hv).trans (ht v (by omega))
    · simp only [chain,formulaEval_append,Bool.and_eq_true]
      exact ⟨hgateτ,hsatτ⟩

lemma clauseToThree_complete (σ : Assignment) {next : ℕ} {c : Clause}
    (hb : clauseBounded next c) (hs : clauseEval σ c = true) :
    ∃ τ : Assignment,AgreeBelow next σ τ ∧ formulaEval τ (clauseToThree next c).1 = true := by
  cases c with
  | nil => simp at hs
  | cons a as => exact chain_complete σ hb hs

theorem toThree_complete (σ : Assignment) {next : ℕ} {F : Formula}
    (hb : variablesBounded next F) (hs : formulaEval σ F = true) :
    ∃ τ : Assignment,AgreeBelow next σ τ ∧ formulaEval τ (toThree next F).1 = true := by
  induction F generalizing next σ with
  | nil => exact ⟨σ,fun _ _ => rfl,rfl⟩
  | cons c cs ih =>
    have hss : clauseEval σ c = true ∧ formulaEval σ cs = true := by simpa using hs
    have hbc := hb c (by simp)
    have hbcs : variablesBounded next cs := fun d hd => hb d (by simp [hd])
    obtain ⟨σ₁,hagree,hfirst⟩ := clauseToThree_complete σ hbc hss.1
    have hnext : next ≤ (clauseToThree next c).2 := by simp
    have htail : variablesBounded (clauseToThree next c).2 cs := variablesBounded_mono hbcs hnext
    have htailSat : formulaEval σ₁ cs = true := by
      rw [← formulaEval_congr hagree hbcs]
      exact hss.2
    obtain ⟨τ,ht,hlast⟩ := ih σ₁ htail htailSat
    have hfirst' : formulaEval τ (clauseToThree next c).1 = true := by
      rw [← formulaEval_congr ht (clauseToThree_bounded hbc)]
      exact hfirst
    refine ⟨τ,?_,?_⟩
    · intro v hv
      exact (hagree v hv).trans (ht v (hv.trans_le hnext))
    · simp only [toThree,formulaEval_append,Bool.and_eq_true]
      exact ⟨hfirst',hlast⟩

/-- Satisfiability preservation, with explicit freshness rather than an oracle
that assumes the existence of a suitable extension. -/
theorem toThree_sat_iff {next : ℕ} {F : Formula} (hb : variablesBounded next F) :
    Sat (toThree next F).1 ↔ Sat F := by
  constructor
  · rintro ⟨σ,hσ⟩
    exact ⟨σ,toThree_sound σ next F hσ⟩
  · rintro ⟨σ,hσ⟩
    obtain ⟨τ,_,hτ⟩ := toThree_complete σ hb hσ
    exact ⟨τ,hτ⟩

lemma chain_clause_count (next : ℕ) (a : Literal) (rest : Clause) :
    (chain next a rest).1.length = 3*rest.length+1 := by
  induction rest generalizing next a with
  | nil => rfl
  | cons b bs ih => simp [chain,orGate,ih]; omega

lemma chain_literal_count (next : ℕ) (a : Literal) (rest : Clause) :
    literalCount (chain next a rest).1 = 7*rest.length+1 := by
  induction rest generalizing next a with
  | nil => rfl
  | cons b bs ih =>
    simp only [chain,literalCount,List.map_append,List.sum_append]
    change 7+literalCount (chain (next+1) (positive next) bs).1 = _
    rw [ih]
    simp only [List.length_cons]
    omega

theorem toThree_size (next : ℕ) (F : Formula) :
    (toThree next F).1.length ≤ 3*literalCount F+F.length ∧
    literalCount (toThree next F).1 ≤ 7*literalCount F+F.length ∧
    freshCount F ≤ literalCount F := by
  induction F generalizing next with
  | nil => simp [toThree,literalCount,freshCount]
  | cons c cs ih =>
    have hh := ih (clauseToThree next c).2
    cases c with
    | nil =>
      simp [toThree,clauseToThree,literalCount,freshCount] at hh ⊢
      omega
    | cons a as =>
      have hc := chain_clause_count next a as
      have hl := chain_literal_count next a as
      simp only [toThree,clauseToThree,List.length_append,List.length_cons]
      simp only [literalCount,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
        freshCount,List.length_cons,Nat.pred_succ,clauseToThree,chain_next] at hh ⊢
      simp only [literalCount] at hl
      omega

end BalancedAssortments.NPCNF

