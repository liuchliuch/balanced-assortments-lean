import BalancedAssortments.CookLevinCorrect

/-! Explicit polynomial clause-count bounds for the actual CNF generator.
These are output-size theorems, not an assumed machine-time implementation. -/
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

lemma length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (h : ∀ x ∈ xs,(f x).length≤B) : (xs.flatMap f).length≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [Nat.add_mul,Nat.one_mul]
    omega

lemma length_allFin_le {n : ℕ} (f : Fin n → Formula) (B : ℕ)
    (h : ∀ i,(f i).length≤B) : (allFin f).length≤n*B := by
  simpa only [allFin,List.length_finRange] using
    length_flatMap_le (List.finRange n) f B (fun i _ => h i)

@[simp] lemma length_guardLiteral (l : Literal) (F : Formula) :
    (guardLiteral l F).length=F.length := by simp [guardLiteral]
@[simp] lemma length_guard {q g W T R : ℕ} (v : Var q g W T R) (F : Formula) :
    (guard v F).length=F.length := by simp [guard]
@[simp] lemma length_force {q g W T R : ℕ} (v : Var q g W T R) :
    (force v).length=1 := rfl

lemma length_copyFamily {q g W T R n : ℕ} (f k : Fin n → Var q g W T R) :
    (copyFamily f k).length≤n := by
  simpa only [Nat.mul_one] using length_allFin_le (fun i => [[neg (f i),pos (k i)]]) 1 (by simp)

lemma length_exactlyOne {q g W T R n : ℕ} (f : Fin n → Var q g W T R) :
    (exactlyOne f).length≤1+n*n := by
  have h := length_allFin_le (fun i => allFin (fun j => if i=j then [] else [[neg (f i),neg (f j)]])) n
    (fun i => by
      simpa only [Nat.mul_one] using length_allFin_le
        (fun j => if i=j then [] else [[neg (f i),neg (f j)]]) 1 (fun j => by by_cases he : i=j <;> simp [he]))
  simpa only [exactlyOne,List.length_append,List.length_singleton] using Nat.add_le_add_left h 1

def shapeClauseBudget (M : Machine) (W T : ℕ) : ℕ :=
  (T+1)*((1+(M.stateExtra+1)^2)+(1+W^2)+W*(1+(M.symbolExtra+3)^2))+
    T*(1+(M.rules.length+1)^2)

lemma length_shapeFormula (M : Machine) (W T : ℕ) :
    (shapeFormula M W T).length≤shapeClauseBudget M W T := by
  have hs := length_allFin_le (fun t : Fin (T+1) =>
    exactlyOne (fun s => (Var.state t s : TVar M W T)) ++
      (exactlyOne (fun p => (Var.head t p : TVar M W T)) ++
        allFin (fun p : Fin W => exactlyOne (fun a => (Var.tape t p a : TVar M W T)))))
    ((1+(M.stateExtra+1)^2)+(1+W^2)+W*(1+(M.symbolExtra+3)^2)) (fun t => by
      have h1 := length_exactlyOne (fun s => (Var.state t s : TVar M W T))
      have h2 := length_exactlyOne (fun p => (Var.head t p : TVar M W T))
      have h3 := length_allFin_le (fun p : Fin W => exactlyOne (fun a => (Var.tape t p a : TVar M W T)))
        (1+(M.symbolExtra+3)^2) (fun p => by simpa [pow_two] using length_exactlyOne (fun a => (Var.tape t p a : TVar M W T)))
      simp only [List.length_append]
      simp only [pow_two] at *
      omega)
  have hc := length_allFin_le (fun t : Fin T => exactlyOne (fun r => (Var.choice t r : TVar M W T)))
    (1+(M.rules.length+1)^2) (fun t => by simpa [pow_two] using length_exactlyOne (fun r => (Var.choice t r : TVar M W T)))
  simpa only [shapeFormula,shapeClauseBudget,List.length_append] using Nat.add_le_add hs hc

lemma length_initialFormula (M : Machine) (W T : ℕ) (c : WindowConfig M W) :
    (initialFormula M W T c).length≤W+2 := by
  have hh := length_allFin_le (fun p => force (Var.tape 0 p (c.tape p) : TVar M W T)) 1 (by simp)
  simp only [initialFormula,List.length_append,length_force,Nat.mul_one] at *
  omega

lemma length_haltBody (M : Machine) {W T : ℕ} (t : Fin T) :
    (haltBody M (W := W) t).length≤1+(M.stateExtra+1)+W+W*(M.symbolExtra+3) := by
  have hs := length_copyFamily (fun s => (Var.state t.castSucc s : TVar M W T)) (fun s => .state t.succ s)
  have hh := length_copyFamily (fun p => (Var.head t.castSucc p : TVar M W T)) (fun p => .head t.succ p)
  have ht := length_allFin_le (fun p : Fin W => copyFamily
    (fun a => (Var.tape t.castSucc p a : TVar M W T)) (fun a => .tape t.succ p a))
    (M.symbolExtra+3) (fun p => length_copyFamily _ _)
  simp only [haltBody,acceptFormula,List.length_append,List.length_singleton]
  omega

lemma length_ruleBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Rule M.stateExtra M.symbolExtra) :
    (ruleBody M (W := W) t r).length≤2+3*W+W*(M.symbolExtra+3) := by
  have hh := length_allFin_le (fun p : Fin W => guard (Var.head t.castSucc p : TVar M W T)
    (force (Var.tape t.castSucc p r.read : TVar M W T) ++
      (force (Var.tape t.succ p r.write : TVar M W T) ++ headTarget M t p r.move))) 3
    (by intro p; simp [headTarget])
  have ht := length_allFin_le (fun p : Fin W => guardLiteral (neg (Var.head t.castSucc p : TVar M W T))
    (copyFamily (fun a => (Var.tape t.castSucc p a : TVar M W T)) (fun a => .tape t.succ p a)))
    (M.symbolExtra+3) (fun p => by
      simpa using (length_copyFamily (fun a => (Var.tape t.castSucc p a : TVar M W T)) (fun a => .tape t.succ p a)))
  simp only [ruleBody,List.length_append,length_force]
  omega

def bodyClauseBudget (M : Machine) (W : ℕ) : ℕ := 3+(M.stateExtra+1)+4*W+W*(M.symbolExtra+3)

lemma length_choiceBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Fin (M.rules.length+1)) :
    (choiceBody M (W := W) t r).length≤bodyClauseBudget M W := by
  refine Fin.cases ?_ (fun i => ?_) r
  · have hh := length_haltBody M (W := W) t
    change (haltBody M t).length≤_
    unfold bodyClauseBudget
    omega
  · have hh := length_ruleBody M (W := W) t M.rules[i.val]
    change (ruleBody M t M.rules[i.val]).length≤_
    unfold bodyClauseBudget
    omega

lemma length_transitionFormula (M : Machine) (W T : ℕ) :
    (transitionFormula M W T).length≤T*((M.rules.length+1)*bodyClauseBudget M W) := by
  apply length_allFin_le
  intro t
  apply length_allFin_le
  intro r
  simpa using length_choiceBody M (W := W) t r

def clauseBudget (M : Machine) (n T : ℕ) : ℕ :=
  let W := n+2*T+1
  shapeClauseBudget M W T+(W+2)+(1+T*((M.rules.length+1)*bodyClauseBudget M W))

/-- Actual clause count, polynomial in input length and the computation clock,
with constants depending only on the fixed finite machine. -/
theorem tableau_clause_count (M : Machine) (word : List Bool) (T : ℕ) :
    (tableauFormula M word T).length≤clauseBudget M word.length T := by
  have hs := length_shapeFormula M (windowWidth word T) T
  have hi := length_initialFormula M (windowWidth word T) T (windowInitial M word T)
  have ht := length_transitionFormula M (windowWidth word T) T
  simp only [tableauFormula,List.length_append,acceptFormula,List.length_singleton]
  unfold clauseBudget
  change _≤shapeClauseBudget M (windowWidth word T) T+(windowWidth word T+2)+
    (1+T*((M.rules.length+1)*bodyClauseBudget M (windowWidth word T)))
  omega

end BalancedAssortments.CookLevin
