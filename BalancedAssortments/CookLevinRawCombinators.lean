import BalancedAssortments.CookLevinBitIndices

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitLiteral BitClause BitFormula)

def rawMap {α β : Type*} (f : α → β × ℕ) : List α → List β × ℕ
  | [] => ([],1)
  | x::xs => let head := f x; let tail := rawMap f xs; (head.1::tail.1,head.2+tail.2+4)
lemma rawMap_eq {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    (rawMap f xs).1=xs.map (fun x => (f x).1) := by induction xs <;> simp_all [rawMap]
lemma rawMap_cost {α β : Type*} (f : α → β × ℕ) (xs : List α) (B : ℕ)
    (h : ∀ x∈xs,(f x).2≤B) : (rawMap f xs).2≤xs.length*(B+4)+1 := by
  induction xs with
  | nil => simp [rawMap]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [rawMap,List.length_cons]
    nlinarith

def rawFlatMap {α β : Type*} (f : α → List β × ℕ) : List α → List β × ℕ
  | [] => ([],1)
  | x::xs => let head := f x; let tail := rawFlatMap f xs
            (head.1++tail.1,head.2+tail.2+head.1.length+4)
lemma rawFlatMap_eq {α β : Type*} (f : α → List β × ℕ) (xs : List α) :
    (rawFlatMap f xs).1=xs.flatMap (fun x => (f x).1) := by induction xs <;> simp_all [rawFlatMap]
lemma rawFlatMap_cost {α β : Type*} (f : α → List β × ℕ) (xs : List α) (B L : ℕ)
    (h : ∀ x∈xs,(f x).2≤B) (hl : ∀ x∈xs,(f x).1.length≤L) :
    (rawFlatMap f xs).2≤xs.length*(B+L+4)+1 := by
  induction xs with
  | nil => simp [rawFlatMap]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxl := hl x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy])) (fun y hy => hl y (by simp [hy]))
    simp only [rawFlatMap,List.length_cons]
    nlinarith

def rawGuard (l : BitLiteral) (F : BitFormula) : BitFormula × ℕ :=
  rawMap (fun c => (l.neg::c,4)) F
lemma rawGuard_decode (l : BitLiteral) (F : BitFormula) :
    (rawGuard l F).1.map (List.map BitLiteral.decode)=
      guardLiteral l.decode (F.map (List.map BitLiteral.decode)) := by
  simp [rawGuard,rawMap_eq,guardLiteral,List.map_map,Function.comp_def]
lemma rawGuard_length (l : BitLiteral) (F : BitFormula) : (rawGuard l F).1.length=F.length := by simp [rawGuard,rawMap_eq]
lemma rawGuard_cost (l : BitLiteral) (F : BitFormula) : (rawGuard l F).2≤8*F.length+1 := by
  have hh := rawMap_cost (fun c : BitClause => (l.neg::c,4)) F 4 (by simp)
  simpa [rawGuard,Nat.mul_comm] using hh

def rawPair (x y : List Bool) : BitFormula × ℕ :=
  let cmp := compareBits x y
  (if cmp.1 == .eq then [] else [[Encoding.bitNegative x,Encoding.bitNegative y]],cmp.2+8)
lemma rawPair_decode (x y : List Bool) :
    (rawPair x y).1.map (List.map BitLiteral.decode)=
      if value x=value y then [] else [[negative (value x),negative (value y)]] := by
  simp only [rawPair,beq_iff_eq,Encoding.compare_eq_iff]
  split <;> simp_all
lemma rawPair_length (x y : List Bool) : (rawPair x y).1.length≤1 := by
  simp only [rawPair]
  split <;> simp
lemma rawPair_cost {x y : List Bool} {b : ℕ} (hx : x.length≤b) (hy : y.length≤b) :
    (rawPair x y).2≤16*b+11 := by
  simp only [rawPair,compareBits_cost]
  omega

def rawExactlyOne (labels : List (List Bool)) : BitFormula × ℕ :=
  let atleast := rawMap (fun x => (Encoding.bitPositive x,2)) labels
  let pairs := rawFlatMap (fun x => rawFlatMap (rawPair x) labels) labels
  (atleast.1::pairs.1,atleast.2+pairs.2+4)

def exactlyOneLabels (labels : List ℕ) : Formula :=
  [labels.map positive] ++ labels.flatMap (fun x => labels.flatMap (fun y =>
    if x=y then [] else [[negative x,negative y]]))

lemma rawExactlyOne_decode (labels : List (List Bool)) :
    (rawExactlyOne labels).1.map (List.map BitLiteral.decode)=exactlyOneLabels (labels.map value) := by
  simp [rawExactlyOne,rawMap_eq,rawFlatMap_eq,exactlyOneLabels,List.map_flatMap,
    List.flatMap_map,List.map_map,Function.comp_def,rawPair_decode]

lemma rawExactlyOne_length (labels : List (List Bool)) :
    (rawExactlyOne labels).1.length≤1+labels.length*labels.length := by
  have h1 : ∀ x,(rawFlatMap (rawPair x) labels).1.length≤labels.length := by
    intro x
    rw [rawFlatMap_eq]
    simpa only [Nat.mul_one] using length_flatMap_le labels (fun y => (rawPair x y).1) 1 (fun y _ => rawPair_length x y)
  have h2 := length_flatMap_le labels (fun x => (rawFlatMap (rawPair x) labels).1) labels.length (fun x _ => h1 x)
  simpa only [rawExactlyOne,List.length_cons,rawFlatMap_eq,Nat.add_comm] using Nat.add_le_add_left h2 1

lemma rawExactlyOne_cost {labels : List (List Bool)} {b : ℕ}
    (h : ∀ x∈labels,x.length≤b) :
    (rawExactlyOne labels).2≤labels.length*(labels.length*(16*b+17)+6)+6*labels.length+6 := by
  have hm := rawMap_cost (fun x : List Bool => (Encoding.bitPositive x,2)) labels 2 (by simp)
  have h1 : ∀ x∈labels,(rawFlatMap (rawPair x) labels).2≤labels.length*(16*b+16)+1 := by
    intro x hx
    exact rawFlatMap_cost (rawPair x) labels (16*b+11) 1
      (fun y hy => rawPair_cost (h x hx) (h y hy)) (fun y _ => rawPair_length x y)
  have hl : ∀ x∈labels,(rawFlatMap (rawPair x) labels).1.length≤labels.length := by
    intro x hx
    rw [rawFlatMap_eq]
    simpa only [Nat.mul_one] using length_flatMap_le labels (fun y => (rawPair x y).1) 1 (fun y _ => rawPair_length x y)
  have ht := rawFlatMap_cost (fun x => rawFlatMap (rawPair x) labels) labels
    (labels.length*(16*b+16)+1) labels.length h1 hl
  simp only [rawExactlyOne]
  nlinarith

end BalancedAssortments.CookLevin
