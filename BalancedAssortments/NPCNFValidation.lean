import BalancedAssortments.NPCNFEncoding

namespace BalancedAssortments.NPCNF.Encoding
open ComplexityTimeBinary

lemma compare_eq_iff (x y : List Bool) : (compareBits x y).1 = .eq ↔ value x = value y := by
  have h := compareBits_correct x y
  cases he : (compareBits x y).1 <;> simp only [he,comparisonMeaning] at h <;> simp <;> omega

def containsLabel (x : List Bool) : List (List Bool) → Bool × ℕ
  | [] => (false,1)
  | y::ys =>
      let cmp := compareBits x y
      let tail := containsLabel x ys
      (decide (cmp.1 = .eq) || tail.1,cmp.2+tail.2+4)

lemma containsLabel_correct (x : List Bool) (xs : List (List Bool)) :
    (containsLabel x xs).1 = true ↔ value x ∈ xs.map value := by
  induction xs with
  | nil => simp [containsLabel]
  | cons y ys ih => simp [containsLabel,compare_eq_iff,ih]

lemma containsLabel_cost {x : List Bool} {xs : List (List Bool)} {b : ℕ}
    (hx : x.length ≤ b) (hxs : ∀ y ∈ xs,y.length ≤ b) :
    (containsLabel x xs).2 ≤ xs.length*(20*(b+1))+1 := by
  induction xs with
  | nil => simp [containsLabel]
  | cons y ys ih =>
    have hy := hxs y (by simp)
    have ht := ih (fun z hz => hxs z (by simp [hz]))
    have hh : max x.length y.length ≤ b := max_le hx hy
    simp only [containsLabel,compareBits_cost,List.length_cons]
    nlinarith

def distinctLabels : List (List Bool) → Bool × ℕ
  | [] => (true,1)
  | x::xs =>
      let member := containsLabel x xs
      let tail := distinctLabels xs
      (!member.1 && tail.1,member.2+tail.2+4)

lemma distinctLabels_correct (xs : List (List Bool)) :
    (distinctLabels xs).1 = true ↔ (xs.map value).Nodup := by
  induction xs with
  | nil => simp [distinctLabels]
  | cons x xs ih =>
    have hm : (containsLabel x xs).1 = false ↔ value x ∉ xs.map value := by
      rw [Bool.eq_false_iff]
      exact not_congr (containsLabel_correct x xs)
    have hn : (!(containsLabel x xs).1) = true ↔ value x ∉ xs.map value := by
      cases he : (containsLabel x xs).1 <;> simp_all
    simp only [distinctLabels,Bool.and_eq_true,List.map_cons,List.nodup_cons,ih,hn]

def checkClause (catalog : List (List Bool)) : BitClause → Bool × ℕ
  | [] => (true,1)
  | l::ls =>
      let member := containsLabel l.labelBits catalog
      let tail := checkClause catalog ls
      (member.1 && tail.1,member.2+tail.2+4)

lemma checkClause_correct (catalog : List (List Bool)) (c : BitClause) :
    (checkClause catalog c).1 = true ↔ ∀ l ∈ c,value l.labelBits ∈ catalog.map value := by
  induction c with
  | nil => simp [checkClause]
  | cons l ls ih => simp [checkClause,containsLabel_correct,ih]

def checkFormula (catalog : List (List Bool)) : BitFormula → Bool × ℕ
  | [] => (true,1)
  | c::cs =>
      let head := checkClause catalog c
      let tail := checkFormula catalog cs
      (head.1 && tail.1,head.2+tail.2+4)

lemma checkFormula_correct (catalog : List (List Bool)) (F : BitFormula) :
    (checkFormula catalog F).1 = true ↔ ∀ c ∈ F,∀ l ∈ c,value l.labelBits ∈ catalog.map value := by
  induction F with
  | nil => simp [checkFormula]
  | cons c cs ih => simp [checkFormula,checkClause_correct,ih]

def validate (input : Raw) : Bool × ℕ :=
  let distinct := distinctLabels input.catalog
  let members := checkFormula input.catalog input.formula
  (distinct.1 && members.1,distinct.2+members.2+4)

theorem validate_correct (input : Raw) : (validate input).1 = true ↔ input.decode.Valid := by
  simp only [validate,Bool.and_eq_true,distinctLabels_correct,checkFormula_correct,
    Catalogued.Valid,Raw.decode]
  constructor
  · rintro ⟨hd,hm⟩
    refine ⟨hd,?_⟩
    intro c hc l hl
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    obtain ⟨l',hl',rfl⟩ := List.mem_map.mp hl
    exact hm c' hc' l' hl'
  · rintro ⟨hd,hm⟩
    refine ⟨hd,?_⟩
    intro c hc l hl
    exact hm (c.map BitLiteral.decode) (List.mem_map.mpr ⟨c,hc,rfl⟩)
      l.decode (List.mem_map.mpr ⟨l,hl,rfl⟩)

def shortClause : BitClause → Bool
  | _::_::_::_::_ => false
  | _ => true

lemma shortClause_correct (c : BitClause) : shortClause c = true ↔ c.length ≤ 3 := by
  cases c with
  | nil => simp [shortClause]
  | cons a as => cases as with
    | nil => simp [shortClause]
    | cons b bs => cases bs with
      | nil => simp [shortClause]
      | cons c cs => cases cs <;> simp [shortClause]

def checkThree : BitFormula → Bool × ℕ
  | [] => (true,1)
  | c::cs => let tail := checkThree cs; (shortClause c && tail.1,tail.2+8)

lemma checkThree_correct (F : BitFormula) :
    (checkThree F).1 = true ↔ ThreeCNF (F.map (List.map BitLiteral.decode)) := by
  induction F with
  | nil => simp [checkThree,ThreeCNF]
  | cons c cs ih => simp [checkThree,shortClause_correct,ThreeCNF] at ih ⊢; intro _; exact ih

/-- Semantic deduplication of raw binary labels, including padded duplicates. -/
def dedupLabels : List (List Bool) → List (List Bool) × ℕ
  | [] => ([],1)
  | x::xs =>
      let tail := dedupLabels xs
      let member := containsLabel x tail.1
      (if member.1 then tail.1 else x::tail.1,tail.2+member.2+4)

lemma dedupLabels_decode (xs : List (List Bool)) :
    (dedupLabels xs).1.map value = (xs.map value).dedup := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := containsLabel_correct x (dedupLabels xs).1
    rw [ih] at hh
    simp only [dedupLabels,List.map_cons,List.dedup_cons']
    by_cases h : value x ∈ (xs.map value).dedup
    · simp [hh.mpr h,h,ih]
    · have hn : (containsLabel x (dedupLabels xs).1).1 = false := Bool.eq_false_iff.mpr (fun he => h (hh.mp he))
      simp [hn,h,ih]

lemma dedupLabels_member {xs : List (List Bool)} {x : List Bool}
    (hx : x ∈ (dedupLabels xs).1) : x ∈ xs := by
  induction xs with
  | nil => simp [dedupLabels] at hx
  | cons y ys ih =>
    simp only [dedupLabels] at hx
    split_ifs at hx
    · exact List.mem_cons_of_mem _ (ih hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem _ (ih hx)

lemma dedupLabels_length (xs : List (List Bool)) : (dedupLabels xs).1.length ≤ xs.length := by
  induction xs with
  | nil => simp [dedupLabels]
  | cons x xs ih => simp only [dedupLabels,List.length_cons];split_ifs <;> (try simp only [List.length_cons]) <;> omega

end BalancedAssortments.NPCNF.Encoding
