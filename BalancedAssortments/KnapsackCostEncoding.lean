import BalancedAssortments.KnapsackCostRefinement
import BalancedAssortments.KnapsackCostScaling

namespace BalancedAssortments.KnapsackCostRational
open ComplexityTimeBinary

theorem encode_width {x : ℚ} {b : ℕ}
    (hn : x.num.natAbs.size ≤ b) (hd : x.den.size ≤ b) : (encode x).Width b := by
  simpa only [Fraction.Width, encode, ← Nat.size_eq_bits_len] using And.intro hn hd

/-- Reduction to canonical rational form can only shorten the numerator and
denominator relative to a positive-denominator unreduced representation. -/
theorem decode_num_den_bounds {x : Fraction} (hx : x.Valid) :
    x.decode.num.natAbs ≤ value x.numerator ∧ x.decode.den ≤ value x.denominator := by
  have hden : (value x.denominator : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have he : x.decode = Rat.divInt (value x.numerator) (value x.denominator) := by
    simp [Fraction.decode, Rat.divInt_eq_div]
  constructor
  · by_cases hz : value x.numerator = 0
    · simp [Fraction.decode, hz]
    · have hh := Rat.num_dvd (value x.numerator : ℤ) hden
      have hb := Int.natAbs_le_of_dvd_ne_zero hh (show (value x.numerator : ℤ) ≠ 0 by exact_mod_cast hz)
      simpa only [← he, Int.natAbs_natCast] using hb
  · have hh := Rat.den_dvd (value x.numerator : ℤ) (value x.denominator : ℤ)
    have hb := Int.le_of_dvd (show (0 : ℤ) < value x.denominator by exact_mod_cast hx) hh
    rw [← he] at hb
    exact_mod_cast hb

theorem decode_bit_bounds {x : Fraction} {b : ℕ} (hx : x.Valid) (hw : x.Width b) :
    x.decode.num.natAbs.size ≤ b ∧ x.decode.den.size ≤ b := by
  have hb := decode_num_den_bounds hx
  have hn := Decomposition.CostBinary.value_lt_pow_length x.numerator
  have hd := Decomposition.CostBinary.value_lt_pow_length x.denominator
  constructor
  · apply Nat.size_le.mpr
    exact (hb.1.trans_lt hn).trans_le (Nat.pow_le_pow_right (by decide) hw.1)
  · apply Nat.size_le.mpr
    exact (hb.2.trans_lt hd).trans_le (Nat.pow_le_pow_right (by decide) hw.2)

end BalancedAssortments.KnapsackCostRational

namespace BalancedAssortments.KnapsackCostState
open KnapsackCostRational ComplexityTimeBinary

/-- The standard input encoding with a genuinely binary-computed scaled profit. -/
def prepareItem (θ : Fraction) (i : Knapsack.Item) : Item × ℕ :=
  let p := encode i.profit
  let k := floorRatio p θ
  (⟨encode i.value, encode i.weight, p, k.1⟩, k.2 + 8)

theorem prepareItem_valid (θ : Fraction) (i : Knapsack.Item) : (prepareItem θ i).1.Valid := by
  exact ⟨encode_valid _, encode_valid _, encode_valid _⟩

theorem prepareItem_decode (θ : Fraction) {i : Knapsack.Item}
    (hv : 0 ≤ i.value) (hw : 0 ≤ i.weight) (hp : 0 ≤ i.profit) :
    (prepareItem θ i).1.decode = i := by
  simp only [prepareItem, Item.decode]
  rw [encode_decode hv, encode_decode hw, encode_decode hp]

theorem prepareItem_scaled {θ : Fraction} {i : Knapsack.Item}
    (hθ : θ.Valid) (hθpos : 0 < θ.decode) (hp : 0 ≤ i.profit) :
    value (prepareItem θ i).1.scaled = Knapsack.scaledProfit θ.decode i := by
  simp only [prepareItem, Knapsack.scaledProfit]
  rw [floorRatio_correct (encode_valid _) hθ hθpos, encode_decode hp]

theorem prepareItem_width {θ : Fraction} {i : Knapsack.Item} {b : ℕ}
    (ht : θ.Width b)
    (hv : (encode i.value).Width b) (hw : (encode i.weight).Width b)
    (hp : (encode i.profit).Width b) : (prepareItem θ i).1.Width (3*b) := by
  exact ⟨Fraction.width_mono hv (by omega), Fraction.width_mono hw (by omega),
    Fraction.width_mono hp (by omega), floorRatio_width hp ht⟩

theorem prepareItem_cost {θ : Fraction} {i : Knapsack.Item} {b : ℕ}
    (ht : θ.Width b) (hp : (encode i.profit).Width b) :
    (prepareItem θ i).2 ≤ 4096 * (b+1)^2 + 8 := by
  exact Nat.add_le_add_right (floorRatio_cost hp ht) 8

/-- Canonical rational bit-size invariants for every actual table entry, not
merely abstract grid values. Scaled-profit preprocessing is also binary. -/
theorem table_rational_bit_bounds {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Knapsack.Item)} {s : Knapsack.State} {b : ℕ}
    (hs : s ∈ Knapsack.table θ capacity bound groups) (hθ : 0 < θ)
    (ht : (encode θ).Width b)
    (hi : ∀ g ∈ groups, ∀ i ∈ g,
      0 ≤ i.value ∧ 0 ≤ i.weight ∧ 0 ≤ i.profit ∧
      (encode i.value).Width b ∧ (encode i.weight).Width b ∧ (encode i.profit).Width b) :
    s.weight.num.natAbs.size ≤ 1 + groups.length * (6*b+1) ∧
    s.weight.den.size ≤ 1 + groups.length * (6*b+1) ∧
    s.profit.num.natAbs.size ≤ 1 + groups.length * (6*b+1) ∧
    s.profit.den.size ≤ 1 + groups.length * (6*b+1) := by
  let enc := fun i => (prepareItem (encode θ) i).1
  have he : ∀ g ∈ groups, ∀ i ∈ g,
      (enc i).Valid ∧ (enc i).Width (3*b) ∧ (enc i).decode = i ∧
      value (enc i).scaled = Knapsack.scaledProfit θ i := by
    intro g hg i hig
    obtain ⟨hv, hw, hp, hvb, hwb, hpb⟩ := hi g hg i hig
    refine ⟨prepareItem_valid _ _, prepareItem_width ht hvb hwb hpb,
      prepareItem_decode _ hv hw hp, ?_⟩
    have hh := prepareItem_scaled (i := i) (encode_valid θ)
      (by rwa [encode_decode hθ.le]) hp
    simpa only [encode_decode hθ.le] using hh
  obtain ⟨bs, hv, heq, hwidth, _⟩ := table_bit_representation enc hs he
  have hw := decode_bit_bounds hv.1 hwidth.1
  have hp := decode_bit_bounds hv.2.1 hwidth.2.1
  have hweq : bs.weight.decode = s.weight := congrArg Knapsack.State.weight heq
  have hpeq : bs.profit.decode = s.profit := congrArg Knapsack.State.profit heq
  rw [hweq] at hw
  rw [hpeq] at hp
  simpa only [show 2*(3*b)+1 = 6*b+1 by omega] using And.intro hw.1 (And.intro hw.2 hp)

end BalancedAssortments.KnapsackCostState
