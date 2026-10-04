import Mathlib

/-! Ordinary CNF over arbitrary natural-number variable labels. There is no
binary max-variable header whose magnitude controls certificate or loop size.
Short/empty clauses and repeated literals have their usual semantics. -/
namespace BalancedAssortments.NPCNF

structure Literal where
  var : ℕ
  positive : Bool
  deriving DecidableEq, Repr

abbrev Assignment := ℕ → Bool
abbrev Clause := List Literal
abbrev Formula := List Clause

def Literal.neg (l : Literal) : Literal := ⟨l.var,!l.positive⟩
def positive (v : ℕ) : Literal := ⟨v,true⟩
def negative (v : ℕ) : Literal := ⟨v,false⟩

def literalEval (σ : Assignment) (l : Literal) : Bool := if l.positive then σ l.var else !σ l.var

def clauseEval (σ : Assignment) (c : Clause) : Bool := c.any (literalEval σ)
def formulaEval (σ : Assignment) (F : Formula) : Bool := F.all (clauseEval σ)

def Sat (F : Formula) : Prop := ∃ σ : Assignment, formulaEval σ F = true

def clauseBounded (n : ℕ) (c : Clause) : Prop := ∀ l ∈ c,l.var < n
def variablesBounded (n : ℕ) (F : Formula) : Prop := ∀ c ∈ F,clauseBounded n c

def ThreeCNF (F : Formula) : Prop := ∀ c ∈ F,c.length ≤ 3

def literalCount (F : Formula) : ℕ := (F.map List.length).sum

def variableLabels (F : Formula) : List ℕ := F.flatten.map Literal.var

def variableCatalog (F : Formula) : List ℕ := (variableLabels F).dedup

@[simp] theorem literalEval_positive (σ : Assignment) (v : ℕ) : literalEval σ (positive v) = σ v := rfl
@[simp] theorem literalEval_negative (σ : Assignment) (v : ℕ) : literalEval σ (negative v) = !σ v := rfl
@[simp] theorem literalEval_neg (σ : Assignment) (l : Literal) : literalEval σ l.neg = !literalEval σ l := by
  cases l with | mk v p => cases p <;> simp [literalEval,Literal.neg]
@[simp] theorem neg_var (l : Literal) : l.neg.var = l.var := rfl
@[simp] theorem positive_var (v : ℕ) : (positive v).var = v := rfl
@[simp] theorem negative_var (v : ℕ) : (negative v).var = v := rfl

@[simp] theorem clauseEval_nil (σ : Assignment) : clauseEval σ [] = false := rfl
@[simp] theorem clauseEval_cons (σ : Assignment) (l : Literal) (ls : Clause) :
    clauseEval σ (l::ls) = (literalEval σ l || clauseEval σ ls) := rfl
@[simp] theorem formulaEval_nil (σ : Assignment) : formulaEval σ [] = true := rfl
@[simp] theorem formulaEval_cons (σ : Assignment) (c : Clause) (cs : Formula) :
    formulaEval σ (c::cs) = (clauseEval σ c && formulaEval σ cs) := rfl
@[simp] theorem formulaEval_append (σ : Assignment) (F G : Formula) :
    formulaEval σ (F++G) = (formulaEval σ F && formulaEval σ G) := by
  simp [formulaEval,List.all_append]

theorem clauseEval_eq_true_iff (σ : Assignment) (c : Clause) :
    clauseEval σ c = true ↔ ∃ l ∈ c,literalEval σ l = true := by simp [clauseEval]

theorem formulaEval_eq_true_iff (σ : Assignment) (F : Formula) :
    formulaEval σ F = true ↔ ∀ c ∈ F,clauseEval σ c = true := by simp [formulaEval]

theorem empty_clause_unsat (F : Formula) (h : [] ∈ F) : ¬ Sat F := by
  rintro ⟨σ,hσ⟩
  have hh := (formulaEval_eq_true_iff σ F).mp hσ [] h
  simp at hh

theorem empty_formula_sat : Sat [] := ⟨fun _ => false,rfl⟩

theorem clauseBounded_mono {m n : ℕ} {c : Clause} (h : clauseBounded m c) (hmn : m ≤ n) :
    clauseBounded n c := fun l hl => (h l hl).trans_le hmn

theorem variablesBounded_mono {m n : ℕ} {F : Formula} (h : variablesBounded m F) (hmn : m ≤ n) :
    variablesBounded n F := fun c hc => clauseBounded_mono (h c hc) hmn

/-- Extending only fresh variables preserves the truth of the original formula. -/
def AgreeBelow (n : ℕ) (σ τ : Assignment) : Prop := ∀ v < n,σ v = τ v

theorem literalEval_congr {n : ℕ} {σ τ : Assignment} {l : Literal}
    (h : AgreeBelow n σ τ) (hl : l.var < n) : literalEval σ l = literalEval τ l := by
  simp only [literalEval,h l.var hl]

theorem clauseEval_congr {n : ℕ} {σ τ : Assignment} {c : Clause}
    (h : AgreeBelow n σ τ) (hc : clauseBounded n c) : clauseEval σ c = clauseEval τ c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    simp only [clauseEval_cons]
    rw [literalEval_congr h (hc l (by simp)), ih (fun x hx => hc x (by simp [hx]))]

theorem formulaEval_congr {n : ℕ} {σ τ : Assignment} {F : Formula}
    (h : AgreeBelow n σ τ) (hF : variablesBounded n F) : formulaEval σ F = formulaEval τ F := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    simp only [formulaEval_cons]
    rw [clauseEval_congr h (hF c (by simp)), ih (fun c hc => hF c (by simp [hc]))]

theorem variableCatalog_nodup (F : Formula) : (variableCatalog F).Nodup := List.nodup_dedup _

theorem mem_variableCatalog {F : Formula} {v : ℕ} :
    v ∈ variableCatalog F ↔ ∃ c ∈ F,∃ l ∈ c,l.var = v := by
  simp only [variableCatalog,List.mem_dedup,variableLabels,List.mem_map,List.mem_flatten]
  constructor
  · rintro ⟨l,⟨c,hc,hl⟩,he⟩; exact ⟨c,hc,l,hl,he⟩
  · rintro ⟨c,hc,l,hl,he⟩; exact ⟨l,⟨c,hc,hl⟩,he⟩

/-- Explicit finite variable catalog. Its length, never the numeric magnitude
of its labels, controls assignment certificates and subsequent digit gadgets. -/
structure Catalogued where
  catalog : List ℕ
  formula : Formula
  deriving DecidableEq, Repr

def Catalogued.Valid (input : Catalogued) : Prop :=
  input.catalog.Nodup ∧ ∀ c ∈ input.formula,∀ l ∈ c,l.var ∈ input.catalog

def Catalogued.Sat (input : Catalogued) : Prop := BalancedAssortments.NPCNF.Sat input.formula

def catalogue (F : Formula) : Catalogued := ⟨variableCatalog F,F⟩

theorem catalogue_valid (F : Formula) : (catalogue F).Valid := by
  refine ⟨variableCatalog_nodup F,?_⟩
  intro c hc l hl
  exact mem_variableCatalog.mpr ⟨c,hc,l,hl,rfl⟩

end BalancedAssortments.NPCNF
