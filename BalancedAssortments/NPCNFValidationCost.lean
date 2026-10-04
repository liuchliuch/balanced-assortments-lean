import BalancedAssortments.NPCNFMeasure

namespace BalancedAssortments.NPCNF.Encoding

lemma distinctLabels_cost {xs : List (List Bool)} {b : ℕ}
    (h : ∀ x ∈ xs,x.length ≤ b) :
    (distinctLabels xs).2 ≤ 32*(xs.length+1)^2*(b+1) := by
  induction xs with
  | nil => simp [distinctLabels]; omega
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs,y.length ≤ b := fun y hy => h y (by simp [hy])
    have hm := containsLabel_cost hx ht
    have hd := ih ht
    simp only [distinctLabels,List.length_cons]
    nlinarith

lemma dedupLabels_cost {xs : List (List Bool)} {b : ℕ}
    (h : ∀ x ∈ xs,x.length ≤ b) :
    (dedupLabels xs).2 ≤ 32*(xs.length+1)^2*(b+1) := by
  induction xs with
  | nil => simp [dedupLabels]; omega
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs,y.length ≤ b := fun y hy => h y (by simp [hy])
    have hd := ih ht
    have hmem : ∀ y ∈ (dedupLabels xs).1,y.length ≤ b := fun y hy => ht y (dedupLabels_member hy)
    have hm := containsLabel_cost hx hmem
    have hl := dedupLabels_length xs
    have hmul := Nat.mul_le_mul_right (20*(b+1)) hl
    simp only [dedupLabels,List.length_cons]
    nlinarith

lemma checkClause_cost {catalog : List (List Bool)} {c : BitClause} {b : ℕ}
    (hc : ∀ x ∈ catalog,x.length ≤ b) (hl : ∀ l ∈ c,l.labelBits.length ≤ b) :
    (checkClause catalog c).2 ≤ c.length*(catalog.length*(20*(b+1))+5)+1 := by
  induction c with
  | nil => simp [checkClause]
  | cons l ls ih =>
    have hh := containsLabel_cost (hl l (by simp)) hc
    have ht := ih (fun l hl' => hl l (by simp [hl']))
    simp only [checkClause,List.length_cons]
    nlinarith

lemma checkFormula_cost {catalog : List (List Bool)} {F : BitFormula} {b : ℕ}
    (hc : ∀ x ∈ catalog,x.length ≤ b) (hf : ∀ c ∈ F,∀ l ∈ c,l.labelBits.length ≤ b) :
    (checkFormula catalog F).2 ≤ bitLiteralCount F*(catalog.length*(20*(b+1))+5)+5*F.length+1 := by
  induction F with
  | nil => simp [checkFormula,bitLiteralCount]
  | cons c cs ih =>
    have hh := checkClause_cost hc (hf c (by simp))
    have ht := ih (fun c hc' l hl => hf c (by simp [hc']) l hl)
    simp only [checkFormula,List.length_cons,bitLiteralCount,List.map_cons,List.sum_cons] at *
    nlinarith

theorem validate_cost (input : Raw) : (validate input).2 ≤ 128*(rawMeasure input+1)^3 := by
  let L := rawMeasure input
  have hw := rawMeasure_widths input
  have hn := rawMeasure_counts input
  have hd := distinctLabels_cost hw.1
  have hf := checkFormula_cost hw.1 hw.2
  have hcat : input.catalog.length ≤ L := hn.1
  have hclauses : input.formula.length ≤ L := hn.2.1
  have hlit : bitLiteralCount input.formula ≤ L := hn.2.2
  have hdsq := Nat.pow_le_pow_left (Nat.add_le_add_right hcat 1) 2
  have hdprod := Nat.mul_le_mul_right (L+1) (Nat.mul_le_mul_left 32 hdsq)
  have hcp := Nat.mul_le_mul_right (20*(L+1)) hcat
  have hfp := Nat.mul_le_mul hlit (Nat.add_le_add_right hcp 5)
  change (distinctLabels input.catalog).2+(checkFormula input.catalog input.formula).2+4 ≤ 128*(L+1)^3
  change (distinctLabels input.catalog).2 ≤ 32*(input.catalog.length+1)^2*(L+1) at hd
  change (checkFormula input.catalog input.formula).2 ≤ bitLiteralCount input.formula*(input.catalog.length*(20*(L+1))+5)+5*input.formula.length+1 at hf
  nlinarith

lemma checkThree_cost (F : BitFormula) : (checkThree F).2 = 8*F.length+1 := by
  induction F <;> simp_all [checkThree] <;> omega

end BalancedAssortments.NPCNF.Encoding
