import Mathlib

/-! Exact row-wise denominator clearing with an explicit binary magnitude bound.
This is algebraic/encoding infrastructure, not an LP optimization theorem. -/
namespace BalancedAssortments.RationalClearing
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def commonDenominator (d : I → ℕ) : ℕ := ∏ i, d i

def clearedNumerator (p : I → ℤ) (d : I → ℕ) (i : I) : ℤ :=
  p i * ∏ j ∈ Finset.univ.erase i, (d j : ℤ)

lemma commonDenominator_pos (d : I → ℕ) (hd : ∀ i, 0 < d i) :
    0 < commonDenominator d := Finset.prod_pos (fun i _ => hd i)

/-- Clearing each coefficient uses the product of the other denominators. -/
theorem clearing_identity (p : I → ℤ) (d : I → ℕ) (hd : ∀ i, 0 < d i) (i : I) :
    (commonDenominator d : ℚ) * ((p i : ℚ) / d i) = (clearedNumerator p d i : ℚ) := by
  have hdi : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
  have hprod : (commonDenominator d : ℚ) =
      (d i : ℚ) * ∏ j ∈ Finset.univ.erase i, (d j : ℚ) := by
    unfold commonDenominator
    push_cast
    exact (Finset.mul_prod_erase Finset.univ (fun j => (d j : ℚ)) (Finset.mem_univ i)).symm
  rw [hprod]
  unfold clearedNumerator
  push_cast
  field_simp

/-- A finite rational row and its integer-cleared row have identical inequality
semantics, including an arbitrary selected RHS coordinate. -/
theorem clear_inequality (p : I → ℤ) (d : I → ℕ) (hd : ∀ i, 0 < d i)
    (s : Finset I) (x : I → ℚ) (rhs : I) :
    (∑ i ∈ s, ((p i : ℚ) / d i) * x i) ≤ (p rhs : ℚ) / d rhs ↔
    (∑ i ∈ s, (clearedNumerator p d i : ℚ) * x i) ≤ (clearedNumerator p d rhs : ℚ) := by
  have hD : (0 : ℚ) < commonDenominator d := by exact_mod_cast commonDenominator_pos d hd
  rw [← mul_le_mul_iff_right₀ hD]
  simp_rw [Finset.mul_sum, ← mul_assoc, clearing_identity p d hd]

/-- Denominator clearing increases per-entry magnitude only by a factor
exponential in the number of row entries; its binary length is linear in it. -/
theorem cleared_abs_le {B : ℕ} (p : I → ℤ) (d : I → ℕ)
    (hp : ∀ i, |p i| ≤ (2 : ℤ) ^ B) (hd : ∀ i, (d i : ℤ) ≤ (2 : ℤ) ^ B) (i : I) :
    |clearedNumerator p d i| ≤ (2 : ℤ) ^ (B * Fintype.card I) := by
  have hprod : |∏ j ∈ Finset.univ.erase i, (d j : ℤ)| ≤
      ((2 : ℤ) ^ B) ^ ((Finset.univ.erase i).card) := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod (s := Finset.univ.erase i)
      (f := fun j => |(d j : ℤ)|) (g := fun _ => (2 : ℤ) ^ B)
      (fun j (_ : j ∈ Finset.univ.erase i) => abs_nonneg (d j : ℤ))
      (fun j (_ : j ∈ Finset.univ.erase i) => by simpa using hd j)
  have hi : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  unfold clearedNumerator
  rw [abs_mul]
  calc |p i| * |∏ j ∈ Finset.univ.erase i, (d j : ℤ)| ≤
        (2 : ℤ) ^ B * ((2 : ℤ) ^ B) ^ ((Finset.univ.erase i).card) :=
      mul_le_mul (hp i) hprod (abs_nonneg _) (by positivity)
       _ = (2 : ℤ) ^ (B * Fintype.card I) := by
         rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
           ← pow_succ', Nat.sub_add_cancel (by omega), ← pow_mul]

/-- Instantiation for the canonical numerator and denominator of actual rationals. -/
theorem rational_clearing_identity (a : I → ℚ) (i : I) :
    (commonDenominator (fun j => (a j).den) : ℚ) * a i =
      (clearedNumerator (fun j => (a j).num) (fun j => (a j).den) i : ℚ) := by
  simpa only [Rat.num_div_den] using
    clearing_identity (fun j => (a j).num) (fun j => (a j).den) (fun j => (a j).den_pos) i

end BalancedAssortments.RationalClearing
