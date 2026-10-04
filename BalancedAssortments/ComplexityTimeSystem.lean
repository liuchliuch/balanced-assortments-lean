import BalancedAssortments.ComplexityTimeVerifier

namespace BalancedAssortments.ComplexityTimeVerifier

/-- Structural dimension check: no unbounded-number comparison is an oracle. -/
def sameLength {α β : Type*} : List α → List β → Bool × ℕ
  | [], [] => (true, 1)
  | _::as, _::bs => let r := sameLength as bs; (r.1,r.2+4)
  | _, _ => (false, 1)

theorem sameLength_correct {α β : Type*} (as : List α) (bs : List β) :
    (sameLength as bs).1 = true ↔ as.length = bs.length := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [sameLength]
  | cons a as ih => cases bs <;> simp [sameLength, ih]

theorem sameLength_cost {α β : Type*} (as : List α) (bs : List β) :
    (sameLength as bs).2 ≤ 4*(as.length+bs.length)+1 := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [sameLength]
  | cons a as ih =>
    cases bs with
    | nil => simp [sameLength]
    | cons b bs =>
      have hh := ih bs
      simp only [sameLength, List.length_cons]
      omega

/-- A shared certificate is zipped with each input row only after its dimension
has been checked. The charge includes structural zip traversal and list overhead. -/
def checkCoefficientRow (as p : List ZBits) (b q : ZBits) : Bool × ℕ :=
  let d := sameLength as p
  if d.1 then
    let r := checkRow (as.zip p) b q
    (r.1,d.2+r.2+4*(as.length+p.length)+4)
  else (false,d.2+4)

def RowHolds (as p : List ZBits) (b q : ZBits) : Prop :=
  as.length = p.length ∧
  ((as.zip p).map (fun v => zvalue v.1*zvalue v.2)).sum ≤ zvalue b*zvalue q

theorem checkCoefficientRow_correct (as p : List ZBits) (b q : ZBits) :
    (checkCoefficientRow as p b q).1 = true ↔ RowHolds as p b q := by
  unfold checkCoefficientRow
  dsimp only
  split_ifs with h
  · have hd := (sameLength_correct as p).mp h
    simp only [checkRow_correct, RowHolds, hd, true_and]
  · have hd : as.length ≠ p.length := by simpa only [sameLength_correct] using h
    simp [RowHolds, hd]

theorem zip_width_bound (as p : List ZBits) (L : ℕ)
    (ha : ∀ a ∈ as, width a ≤ L) (hp : ∀ x ∈ p, width x ≤ L) :
    ∀ v ∈ as.zip p, width v.1 ≤ L ∧ width v.2 ≤ L := by
  intro v hv
  exact ⟨ha _ (List.of_mem_zip hv).1, hp _ (List.of_mem_zip hv).2⟩

/-- A uniform polynomial for one entire row, including dimension validation,
shared-certificate pairing and bitwise arithmetic. -/
def rowBudget (N L : ℕ) : ℕ :=
  (N+1)*(5000*(L+1)^2+256*(3*L+2*N+1)+500)

theorem checkCoefficientRow_cost (as p : List ZBits) (b q : ZBits) (N L : ℕ)
    (han : as.length ≤ N) (hpn : p.length ≤ N)
    (ha : ∀ a ∈ as, width a ≤ L) (hp : ∀ x ∈ p, width x ≤ L)
    (hb : width b ≤ L) (hq : width q ≤ L) :
    (checkCoefficientRow as p b q).2 ≤ rowBudget N L := by
  have hd := sameLength_cost as p
  have hz : (as.zip p).length ≤ N := by simp only [List.length_zip]; omega
  have hc := checkRow_cost (as.zip p) b q L (zip_width_bound as p L ha hp) hb hq
  have hb1 : ((as.zip p).length+1)*(4000*(L+1)^2+128*(3*L+2*(as.zip p).length+1)+200) ≤
      (N+1)*(4000*(L+1)^2+128*(3*L+2*N+1)+200) := by
    exact Nat.mul_le_mul (by omega) (by omega)
  unfold checkCoefficientRow rowBudget
  dsimp only
  split_ifs <;> nlinarith

def checkRows (p : List ZBits) (q : ZBits) : List (List ZBits × ZBits) → Bool × ℕ
  | [] => (true,1)
  | (as,b)::rows =>
      let c := checkCoefficientRow as p b q
      let r := checkRows p q rows
      (c.1 && r.1,c.2+r.2+4)

theorem checkRows_correct (p : List ZBits) (q : ZBits) (rows : List (List ZBits × ZBits)) :
    (checkRows p q rows).1 = true ↔ ∀ row ∈ rows, RowHolds row.1 p row.2 q := by
  induction rows with
  | nil => simp [checkRows]
  | cons row rows ih => simp [checkRows, checkCoefficientRow_correct, ih]

theorem checkRows_cost (p : List ZBits) (q : ZBits) (rows : List (List ZBits × ZBits)) (N L : ℕ)
    (hpN : p.length ≤ N) (hp : ∀ x ∈ p, width x ≤ L) (hq : width q ≤ L)
    (hr : ∀ row ∈ rows, row.1.length ≤ N ∧ (∀ a ∈ row.1, width a ≤ L) ∧ width row.2 ≤ L) :
    (checkRows p q rows).2 ≤ rows.length*(rowBudget N L+4)+1 := by
  induction rows with
  | nil => simp [checkRows]
  | cons row rows ih =>
    have hh := hr row (by simp)
    have hi := ih (fun r h => hr r (by simp [h]))
    have hc := checkCoefficientRow_cost row.1 p row.2 q N L hh.1 hpN hh.2.1 hp hh.2.2 hq
    simp only [checkRows, List.length_cons]
    nlinarith

/-- Whole-system verifier: one positive common denominator and the same numerator
list for every row. Its acceptance condition is exactly the integer-cleared LP. -/
def checkSystem (p : List ZBits) (q : ZBits) (rows : List (List ZBits × ZBits)) : Bool × ℕ :=
  let d := zle q zzero
  if d.1 then (false,d.2+4) else
    let r := checkRows p q rows
    (r.1,d.2+r.2+4)

theorem checkSystem_correct (p : List ZBits) (q : ZBits) (rows : List (List ZBits × ZBits)) :
    (checkSystem p q rows).1 = true ↔
      0 < zvalue q ∧ ∀ row ∈ rows, RowHolds row.1 p row.2 q := by
  have hz : zvalue zzero = 0 := by simp [zvalue, zzero, ComplexityTimeBinary.value]
  unfold checkSystem
  dsimp only
  split_ifs with h
  · have hq := (zle_correct q zzero).mp h
    simp only [hz] at hq
    simp [not_lt.mpr hq]
  · have hq : 0 < zvalue q := by
      have hn : ¬ zvalue q ≤ zvalue zzero := fun hh => h ((zle_correct q zzero).mpr hh)
      rw [hz] at hn
      omega
    simp [checkRows_correct, hq]

theorem checkSystem_cost (p : List ZBits) (q : ZBits) (rows : List (List ZBits × ZBits)) (N L : ℕ)
    (hpN : p.length ≤ N) (hp : ∀ x ∈ p, width x ≤ L) (hq : width q ≤ L)
    (hr : ∀ row ∈ rows, row.1.length ≤ N ∧ (∀ a ∈ row.1, width a ≤ L) ∧ width row.2 ≤ L) :
    (checkSystem p q rows).2 ≤ rows.length*(rowBudget N L+4)+48*L+27 := by
  have hd := zle_cost q zzero
  have hw : width zzero = 0 := rfl
  rw [hw, max_eq_left (Nat.zero_le _)] at hd
  have hc := checkRows_cost p q rows N L hpN hp hq hr
  unfold checkSystem
  dsimp only
  split_ifs <;> nlinarith

end BalancedAssortments.ComplexityTimeVerifier
