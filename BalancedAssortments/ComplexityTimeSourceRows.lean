import BalancedAssortments.ComplexityTimeFractions
import BalancedAssortments.DecisionPolyhedron

/-! Source decision rows generated with raw bit fractions and explicit bounded
list lookup. This layer performs no canonical-rational arithmetic. -/
namespace BalancedAssortments.ComplexityTimeSourceRows
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions DecisionPolyhedron

/-- Bounded unary index traversal of the actual input list. -/
def lookup {α : Type*} (fallback : α) : List α → ℕ → α × ℕ
  | [], _ => (fallback,1)
  | x::_, 0 => (x,1)
  | _::xs, i+1 => let r := lookup fallback xs i; (r.1,r.2+4)

theorem lookup_value {α : Type*} (fallback : α) (xs : List α) (i : ℕ) :
    (lookup fallback xs i).1 = xs.getD i fallback := by
  induction xs generalizing i with
  | nil => simp [lookup]
  | cons x xs ih => cases i <;> simp [lookup,ih]

theorem lookup_cost {α : Type*} (fallback : α) (xs : List α) (i : ℕ) :
    (lookup fallback xs i).2 ≤ 4*xs.length+1 := by
  induction xs generalizing i with
  | nil => simp [lookup]
  | cons x xs ih =>
    cases i with
    | zero => simp [lookup]
    | succ i => have h := ih i; simp only [lookup,List.length_cons]; omega

theorem lookup_property {α : Type*} (P : α → Prop) (fallback : α) (xs : List α) (i : ℕ)
    (hf : P fallback) (hx : ∀ x ∈ xs, P x) : P (lookup fallback xs i).1 := by
  induction xs generalizing i with
  | nil => exact hf
  | cons x xs ih =>
    cases i with
    | zero => exact hx x (by simp)
    | succ i => exact ih i (fun y hy => hx y (by simp [hy]))

/-- Equality of bounded unary row/column indices. -/
def eqIndex : ℕ → ℕ → Bool × ℕ
  | 0,0 => (true,1)
  | i+1,j+1 => let r := eqIndex i j; (r.1,r.2+4)
  | _,_ => (false,1)

theorem eqIndex_value (i j : ℕ) : (eqIndex i j).1 = decide (i=j) := by
  induction i generalizing j with
  | zero => cases j <;> simp [eqIndex]
  | succ i ih => cases j <;> simp [eqIndex,ih]

theorem eqIndex_cost (i j : ℕ) : (eqIndex i j).2 ≤ 4*(i+j)+1 := by
  induction i generalizing j with
  | zero => cases j <;> simp [eqIndex]
  | succ i ih =>
    cases j with
    | zero => simp [eqIndex]
    | succ j => have h := ih j; simp only [eqIndex]; omega

def support (mask : List Bool) (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (lookup false mask i.val).1)

def coefficientRaw {n : ℕ} (v r : List Fraction) (α H : Fraction) (mask : List Bool)
    (row : Row n) (j : Fin n) : Fraction × ℕ :=
  match row with
  | .nonnegative i =>
      let e := eqIndex j.val i.val
      (if e.1 then negative one else zero,e.2+4)
  | .cap i =>
      let e := eqIndex j.val i.val
      (if e.1 then one else zero,e.2+4)
  | .rank =>
      let x := lookup zero v j.val
      let y := reciprocalPositive x.1
      (y.1,x.2+y.2+4)
  | .balance i k =>
      let a := lookup false mask i.val
      let b := lookup false mask k.val
      if a.1 && b.1 then
        let u := eqIndex j.val k.val
        let z := eqIndex j.val i.val
        let s := subtract (if u.1 then α else zero) (if z.1 then one else zero)
        (s.1,a.2+b.2+u.2+z.2+s.2+10)
      else (zero,a.2+b.2+4)
  | .offsupport i =>
      let a := lookup false mask i.val
      if a.1 then (zero,a.2+4) else
        let e := eqIndex j.val i.val
        (if e.1 then one else zero,a.2+e.2+4)
  | .target =>
      let x := lookup zero r j.val
      let s := subtract H x.1
      (s.1,x.2+s.2+4)

theorem positive_num (x : Fraction) (hv : Valid x) (hx : 0 < decode x) : 0 < zvalue x.num := by
  have hd : (0 : ℚ) < value x.den := by exact_mod_cast hv
  have hn : (0 : ℚ) < (zvalue x.num : ℚ) := by
    have h := mul_pos hx hd
    simpa only [decode,div_mul_cancel₀ _ (ne_of_gt hd)] using h
  exact_mod_cast hn

/-- Exact semantic connection of generated raw rows to the source model. -/
theorem coefficientRaw_spec {n : ℕ} (v r : List Fraction) (α H : Fraction) (mask : List Bool)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (row : Row n) (j : Fin n) :
    Valid (coefficientRaw v r α H mask row j).1 ∧
    decode (coefficientRaw v r α H mask row j).1 =
      coefficient (fun j => decode (lookup zero v j.val).1)
        (fun j => decode (lookup zero r j.val).1) (decode α) (decode H) (support mask n) row j := by
  cases row with
  | nonnegative i =>
    simp only [coefficientRaw,coefficient,eqIndex_value]
    by_cases h : j=i <;> simp [h,Fin.val_inj]
  | cap i =>
    simp only [coefficientRaw,coefficient,eqIndex_value]
    by_cases h : j=i <;> simp [h,Fin.val_inj]
  | rank =>
    exact ⟨reciprocalPositive_valid _ (positive_num _ (hv j).1 (hv j).2),
      reciprocalPositive_decode _ (positive_num _ (hv j).1 (hv j).2)⟩
  | balance i k =>
    by_cases h : (lookup false mask i.val).1 = true ∧ (lookup false mask k.val).1 = true
    · simp only [coefficientRaw,coefficient,support,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true,h,↓reduceIte,eqIndex_value,decide_eq_true_eq,Fin.val_inj]
      have hu : Valid (if j=k then α else zero) := by split_ifs <;> simp_all
      have hz : Valid (if j=i then one else zero) := by split_ifs <;> simp
      refine ⟨subtract_valid _ _ hu hz, ?_⟩
      rw [subtract_decode _ _ hu hz]
      split_ifs <;> simp
    · simp [coefficientRaw,coefficient,support,Bool.and_eq_true,h]
  | offsupport i =>
    by_cases h : (lookup false mask i.val).1 = true
    · simp [coefficientRaw,coefficient,support,h]
    · simp only [coefficientRaw,coefficient,support,Finset.mem_filter,Finset.mem_univ,true_and,
        h,↓reduceIte,eqIndex_value,decide_eq_true_eq,Fin.val_inj]
      split_ifs <;> simp
  | target =>
    exact ⟨subtract_valid _ _ hH (hr j),subtract_decode _ _ hH (hr j)⟩

def fromNatural (bits : List Bool) : Fraction := ⟨(bits,[]),[true]⟩
@[simp] theorem fromNatural_decode (bits : List Bool) : decode (fromNatural bits) = (value bits : ℚ) := by
  simp [decode,fromNatural,zvalue,value]
@[simp] theorem fromNatural_valid (bits : List Bool) : Valid (fromNatural bits) := by
  simp [Valid,fromNatural,value]
@[simp] theorem fromNatural_width (bits : List Bool) : ComplexityTimeFractions.width (fromNatural bits) = max bits.length 1 := by
  simp [ComplexityTimeFractions.width,ComplexityTimeVerifier.width,fromNatural]

def boundRaw {n : ℕ} (v : List Fraction) (K : List Bool) (H : Fraction) (row : Row n) : Fraction × ℕ :=
  match row with
  | .cap i => lookup zero v i.val
  | .rank => (fromNatural K,4)
  | .target => (negative H,4)
  | _ => (zero,4)

theorem boundRaw_spec {n : ℕ} (v : List Fraction) (K : List Bool) (H : Fraction)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1) (hH : Valid H) (row : Row n) :
    Valid (boundRaw v K H row).1 ∧ decode (boundRaw v K H row).1 =
      bound (fun j => decode (lookup zero v j.val).1) (value K) (decode H) row := by
  cases row <;> simp [boundRaw,bound,hv,hH]

lemma lookup_width (xs : List Fraction) (B i : ℕ)
    (hx : ∀ x ∈ xs, ComplexityTimeFractions.width x ≤ B) :
    ComplexityTimeFractions.width (lookup zero xs i).1 ≤ B+1 := by
  apply lookup_property (fun x => ComplexityTimeFractions.width x ≤ B+1) zero xs i
  · simp
  · intro x h
    exact (hx x h).trans (by omega)

def scalarBudget (n B : ℕ) : ℕ := 4000*(B+2)^2+32*n+50

set_option maxHeartbeats 1000000 in
theorem coefficientRaw_bounds {n B : ℕ} (v r : List Fraction) (α H : Fraction) (mask : List Bool)
    (hvn : v.length ≤ n) (hrn : r.length ≤ n) (hmn : mask.length ≤ n)
    (hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ B)
    (hr : ∀ x ∈ r, ComplexityTimeFractions.width x ≤ B)
    (hα : ComplexityTimeFractions.width α ≤ B) (hH : ComplexityTimeFractions.width H ≤ B)
    (row : Row n) (j : Fin n) :
    ComplexityTimeFractions.width (coefficientRaw v r α H mask row j).1 ≤ 3*B+5 ∧
    (coefficientRaw v r α H mask row j).2 ≤ scalarBudget n B := by
  have hlookup (xs : List Fraction) (hn : xs.length ≤ n) (i : ℕ) :
      (lookup zero xs i).2 ≤ 4*n+1 := (lookup_cost zero xs i).trans (by omega)
  have hm (i : ℕ) : (lookup false mask i).2 ≤ 4*n+1 := (lookup_cost false mask i).trans (by omega)
  have he (i k : Fin n) : (eqIndex i.val k.val).2 ≤ 8*n+1 := by
    have h := eqIndex_cost i.val k.val
    have hi := i.isLt
    have hk := k.isLt
    omega
  have hz : ComplexityTimeFractions.width zero ≤ B+1 := by simp
  have ho : ComplexityTimeFractions.width one ≤ B+1 := by simp
  cases row with
  | nonnegative i =>
    have hh := he j i
    simp only [coefficientRaw]
    split_ifs <;> simp only [negative_width,one_width,zero_width] <;>
      constructor <;> (try unfold scalarBudget) <;> nlinarith
  | cap i =>
    have hh := he j i
    simp only [coefficientRaw]
    split_ifs <;> simp only [one_width,zero_width] <;>
      constructor <;> (try unfold scalarBudget) <;> nlinarith
  | rank =>
    have hl := hlookup v hvn j.val
    have hw := lookup_width v B j.val hv
    have hrw := reciprocalPositive_width (lookup zero v j.val).1
    have hrc := reciprocalPositive_cost (lookup zero v j.val).1
    simp only [coefficientRaw]
    constructor
    · omega
    · unfold scalarBudget
      nlinarith
  | balance i k =>
    have hmi := hm i.val
    have hmk := hm k.val
    have hei := he j i
    have hek := he j k
    have hu : ComplexityTimeFractions.width (if (eqIndex j.val k.val).1 then α else zero) ≤ B+1 := by
      split_ifs <;> omega
    have hz' : ComplexityTimeFractions.width (if (eqIndex j.val i.val).1 then one else zero) ≤ B+1 := by
      split_ifs <;> omega
    have hsw := subtract_width _ _ (B+1) hu hz'
    have hsc := subtract_cost _ _ (B+1) hu hz'
    by_cases h : ((lookup false mask i.val).1 && (lookup false mask k.val).1) = true
    · simp only [coefficientRaw,h,↓reduceIte]
      constructor
      · omega
      · unfold scalarBudget
        nlinarith
    · simp only [coefficientRaw,h,Bool.false_eq_true,if_false,zero_width]
      constructor
      · omega
      · unfold scalarBudget
        omega
  | offsupport i =>
    have hmi := hm i.val
    have hei := he j i
    simp only [coefficientRaw]
    split_ifs <;> simp only [one_width,zero_width] <;>
      constructor <;> (try unfold scalarBudget) <;> nlinarith
  | target =>
    have hl := hlookup r hrn j.val
    have hw := lookup_width r B j.val hr
    have hHH : ComplexityTimeFractions.width H ≤ B+1 := hH.trans (by omega)
    have hsw := subtract_width H _ (B+1) hHH hw
    have hsc := subtract_cost H _ (B+1) hHH hw
    simp only [coefficientRaw]
    constructor
    · omega
    · unfold scalarBudget
      nlinarith

theorem boundRaw_bounds {n B : ℕ} (v : List Fraction) (K : List Bool) (H : Fraction)
    (hvn : v.length ≤ n) (hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ B)
    (hK : K.length ≤ B) (hH : ComplexityTimeFractions.width H ≤ B) (row : Row n) :
    ComplexityTimeFractions.width (boundRaw v K H row).1 ≤ 3*B+5 ∧
    (boundRaw v K H row).2 ≤ scalarBudget n B := by
  cases row with
  | cap i =>
    have hw := lookup_width v B i.val hv
    have hc := lookup_cost zero v i.val
    simp only [boundRaw]
    constructor
    · omega
    · unfold scalarBudget; nlinarith
  | rank => simp only [boundRaw,fromNatural_width]; constructor <;> (try unfold scalarBudget) <;> omega
  | target => simp only [boundRaw,negative_width]; constructor <;> (try unfold scalarBudget) <;> omega
  | nonnegative i => simp only [boundRaw,zero_width]; constructor <;> (try unfold scalarBudget) <;> omega
  | balance i k => simp only [boundRaw,zero_width]; constructor <;> (try unfold scalarBudget) <;> omega
  | offsupport i => simp only [boundRaw,zero_width]; constructor <;> (try unfold scalarBudget) <;> omega

end BalancedAssortments.ComplexityTimeSourceRows
