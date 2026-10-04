import BalancedAssortments.PolyhedralBasisRational

/-! Closure rules for canonical rational coefficient bit bounds. -/
namespace BalancedAssortments.PolyhedralBasis

lemma canonical_fraction_bounds (p q : ℤ) (hq : q ≠ 0) :
    |(Rat.divInt p q).num| ≤ |p| ∧ ((Rat.divInt p q).den : ℤ) ≤ |q| := by
  constructor
  · by_cases hp : p = 0
    · simp [hp]
    · have h := Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd p hq) hp
      have hh : ((Rat.divInt p q).num.natAbs : ℤ) ≤ (p.natAbs : ℤ) := by exact_mod_cast h
      simpa only [Int.natCast_natAbs] using hh
  · have h := Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd p q) hq
    have hh : ((Rat.divInt p q).den : ℤ) ≤ (q.natAbs : ℤ) := by exact_mod_cast h
    simpa only [Int.natCast_natAbs] using hh

lemma CoeffBound.of_fraction {B : ℕ} {p q : ℤ} (hq : q ≠ 0)
    (hpB : |p| ≤ (2 : ℤ) ^ B) (hqB : |q| ≤ (2 : ℤ) ^ B) :
    CoeffBound B (Rat.divInt p q) := by
  have h := canonical_fraction_bounds p q hq
  exact ⟨h.1.trans hpB, h.2.trans hqB⟩

lemma CoeffBound.mono {B C : ℕ} {a : ℚ} (h : CoeffBound B a) (hBC : B ≤ C) :
    CoeffBound C a := by
  have hp : (2 : ℤ) ^ B ≤ 2 ^ C := pow_le_pow_right₀ (by norm_num) hBC
  exact ⟨h.1.trans hp, h.2.trans hp⟩

lemma CoeffBound.zero (B : ℕ) : CoeffBound B 0 := by
  constructor
  · simp
  · simp; exact one_le_pow₀ (by norm_num)

lemma CoeffBound.one (B : ℕ) : CoeffBound B 1 := by
  have h : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  simpa [CoeffBound] using And.intro h h

lemma CoeffBound.neg {B : ℕ} {a : ℚ} (h : CoeffBound B a) : CoeffBound B (-a) := by
  simpa [CoeffBound] using h

lemma CoeffBound.inv {B : ℕ} {a : ℚ} (h : CoeffBound B a) : CoeffBound B a⁻¹ := by
  by_cases ha : a = 0
  · simp only [ha, inv_zero]; exact CoeffBound.zero B
  · have hn : a.num ≠ 0 := by intro hn; exact ha (Rat.zero_of_num_zero hn)
    rw [Rat.inv_def]
    apply CoeffBound.of_fraction hn
    · simpa using h.2
    · exact h.1

lemma CoeffBound.add {B C : ℕ} {a b : ℚ} (ha : CoeffBound B a) (hb : CoeffBound C b) :
    CoeffBound (B + C + 1) (a + b) := by
  have hda : (0 : ℤ) < a.den := by exact_mod_cast a.den_pos
  have hdb : (0 : ℤ) < b.den := by exact_mod_cast b.den_pos
  have he : a + b = Rat.divInt (a.num * b.den + b.num * a.den) (a.den * b.den) := by
    calc a + b = (a.num : ℚ) / a.den + (b.num : ℚ) / b.den := by
           rw [Rat.num_div_den, Rat.num_div_den]
         _ = _ := by
           rw [Rat.divInt_eq_div]
           push_cast
           field_simp
           <;> ring
  rw [he]
  apply CoeffBound.of_fraction (mul_ne_zero hda.ne' hdb.ne')
  · calc |a.num * (b.den : ℤ) + b.num * (a.den : ℤ)| ≤
          |a.num * (b.den : ℤ)| + |b.num * (a.den : ℤ)| := abs_add_le _ _
         _ = |a.num| * (b.den : ℤ) + |b.num| * (a.den : ℤ) := by
           rw [abs_mul, abs_mul, abs_of_pos hda, abs_of_pos hdb]
         _ ≤ 2 ^ B * 2 ^ C + 2 ^ C * 2 ^ B := by
           gcongr
           · exact ha.1
           · exact hb.2
           · exact hb.1
           · exact ha.2
         _ = (2 : ℤ) ^ (B+C+1) := by rw [pow_succ, pow_add]; ring
  · have hmul : (a.den : ℤ) * b.den ≤ (2 : ℤ) ^ B * 2 ^ C :=
      mul_le_mul ha.2 hb.2 hdb.le (by positivity)
    rw [abs_of_pos (mul_pos hda hdb), ← pow_add] at *
    exact hmul.trans (pow_le_pow_right₀ (by norm_num) (by omega))

lemma CoeffBound.sub {B C : ℕ} {a b : ℚ} (ha : CoeffBound B a) (hb : CoeffBound C b) :
    CoeffBound (B+C+1) (a-b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

lemma CoeffBound.of_sizes {B : ℕ} {a : ℚ}
    (hn : a.num.natAbs.size ≤ B) (hd : a.den.size ≤ B) : CoeffBound B a := by
  have hn' := (Nat.size_le.mp hn).le
  have hd' := (Nat.size_le.mp hd).le
  constructor
  · have hh : (a.num.natAbs : ℤ) ≤ (2 : ℤ) ^ B := by exact_mod_cast hn'
    simpa only [Int.natCast_natAbs] using hh
  · exact_mod_cast hd'

lemma CoeffBound.mul {B C : ℕ} {a b : ℚ} (ha : CoeffBound B a) (hb : CoeffBound C b) :
    CoeffBound (B+C) (a*b) := by
  have hda : (a.den : ℤ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hdb : (b.den : ℤ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  have he : a*b = Rat.divInt (a.num*b.num) (a.den*b.den) := by
    calc a*b = Rat.divInt a.num a.den * Rat.divInt b.num b.den := by
           rw [Rat.num_divInt_den, Rat.num_divInt_den]
         _ = _ := Rat.divInt_mul_divInt _ _
  rw [he]
  apply CoeffBound.of_fraction (mul_ne_zero hda hdb)
  · rw [abs_mul, pow_add]
    exact mul_le_mul ha.1 hb.1 (abs_nonneg _) (by positivity)
  · rw [abs_mul, Nat.abs_cast, Nat.abs_cast, pow_add]
    exact mul_le_mul ha.2 hb.2 (by positivity) (by positivity)

lemma CoeffBound.div {B C : ℕ} {a b : ℚ} (ha : CoeffBound B a) (hb : CoeffBound C b) :
    CoeffBound (B+C) (a/b) := by
  rw [div_eq_mul_inv]
  exact ha.mul hb.inv

lemma CoeffBound.pow {B : ℕ} {a : ℚ} (ha : CoeffBound B a) (j : ℕ) :
    CoeffBound (B*j) (a^j) := by
  induction j with
  | zero => simpa using CoeffBound.one 0
  | succ j ih =>
    rw [pow_succ]
    simpa [Nat.mul_add, Nat.mul_one] using ih.mul ha

lemma CoeffBound.sizes {B : ℕ} {a : ℚ} (h : CoeffBound B a) :
    a.num.natAbs.size ≤ B+1 ∧ a.den.size ≤ B+1 := by
  have hn : a.num.natAbs ≤ 2^B := by
    have hh : (a.num.natAbs : ℤ) ≤ (2:ℤ)^B := by simpa using h.1
    exact_mod_cast hh
  have hd : a.den ≤ 2^B := by exact_mod_cast h.2
  have hp : 0 < 2^B := Nat.two_pow_pos B
  constructor <;> apply Nat.size_le.mpr <;> rw [pow_succ] <;> omega

lemma CoeffBound.min {B : ℕ} {a b : ℚ} (ha : CoeffBound B a) (hb : CoeffBound B b) :
    CoeffBound B (min a b) := by
  rcases le_total a b with h | h
  · simpa [min_eq_left h] using ha
  · simpa [min_eq_right h] using hb

lemma CoeffBound.max {B : ℕ} {a b : ℚ} (ha : CoeffBound B a) (hb : CoeffBound B b) :
    CoeffBound B (max a b) := by
  rcases le_total a b with h | h
  · simpa [max_eq_right h] using hb
  · simpa [max_eq_left h] using ha

end BalancedAssortments.PolyhedralBasis
