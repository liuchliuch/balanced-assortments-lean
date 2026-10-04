import BalancedAssortments.ComplexityTimeTotalCertificates

/-! Algebra for the division-free streaming witness verifier. The accumulator
uses fresh integer factors and never normalizes or divides an operand at runtime. -/
namespace BalancedAssortments.DirectVerifier
open scoped BigOperators

/-- Denominator/product and cleared numerator for a sum of integer ratios. -/
def sumStep (acc term : ℤ×ℤ) : ℤ×ℤ :=
  (term.1*acc.1,term.1*acc.2+term.2*acc.1)

def sumFold (terms : List (ℤ×ℤ)) (acc : ℤ×ℤ) : ℤ×ℤ := terms.foldl sumStep acc

lemma sumStep_ratio (acc term : ℤ×ℤ) (ha : acc.1≠0) (ht : term.1≠0) :
    ((sumStep acc term).2 : ℚ)/(sumStep acc term).1 =
      (acc.2 : ℚ)/acc.1+(term.2 : ℚ)/term.1 := by
  have haq : (acc.1 : ℚ)≠0 := by exact_mod_cast ha
  have htq : (term.1 : ℚ)≠0 := by exact_mod_cast ht
  simp only [sumStep,Int.cast_add,Int.cast_mul]
  field_simp
  <;> ring

/-- Positivity and exact rational meaning for arbitrary prefixes. This also
covers the empty record stream and zero or negative summands. -/
theorem sumFold_spec (terms : List (ℤ×ℤ)) (acc : ℤ×ℤ)
    (ha : 0<acc.1) (ht : ∀ t ∈ terms,0<t.1) :
    0<(sumFold terms acc).1 ∧
      ((sumFold terms acc).2 : ℚ)/(sumFold terms acc).1 =
        (acc.2 : ℚ)/acc.1+(terms.map (fun t => (t.2 : ℚ)/t.1)).sum := by
  induction terms generalizing acc with
  | nil => simp [sumFold,ha]
  | cons t ts ih =>
    have ht0 := ht t (by simp)
    have hstep : 0<(sumStep acc t).1 := mul_pos ht0 ha
    have hh := ih (sumStep acc t) hstep (fun u hu => ht u (by simp [hu]))
    simp only [sumFold,List.foldl_cons,List.map_cons,List.sum_cons] at hh ⊢
    refine ⟨hh.1,?_⟩
    rw [hh.2,sumStep_ratio acc t (ne_of_gt ha) (ne_of_gt ht0)]
    ring

/-- A common positive denominator converts the aggregate rational inequality
into one integer comparison, without division in the checker. -/
theorem sumFold_bound_iff (terms : List (ℤ×ℤ)) (ht : ∀ t ∈ terms,0<t.1) (b : ℤ) :
    (sumFold terms (1,0)).2≤b*(sumFold terms (1,0)).1 ↔
      (terms.map (fun t => (t.2 : ℚ)/t.1)).sum≤(b : ℚ) := by
  have hh := sumFold_spec terms (1,0) (by norm_num) ht
  have hd : (0 : ℚ)<(sumFold terms (1,0)).1 := by exact_mod_cast hh.1
  have he : ((sumFold terms (1,0)).2 : ℚ)/(sumFold terms (1,0)).1=
      (terms.map (fun t => (t.2 : ℚ)/t.1)).sum := by simpa using hh.2
  rw [← he,div_le_iff₀ hd]
  exact_mod_cast Iff.rfl

/-- The fixed shared positive witness denominator can be kept signed. -/
theorem revenue_cleared_iff (terms : List (ℤ×ℤ)) (ht : ∀ t ∈ terms,0<t.1)
    (q total hn hd : ℤ) (hhd : 0<hd) :
    hn*(sumFold terms (1,0)).1*(q+total)≤(sumFold terms (1,0)).2*hd ↔
      (hn : ℚ)/hd*((q : ℚ)+total)≤(terms.map (fun t => (t.2 : ℚ)/t.1)).sum := by
  have hh := sumFold_spec terms (1,0) (by norm_num) ht
  have hD : (0 : ℚ)<(sumFold terms (1,0)).1 := by exact_mod_cast hh.1
  have hhD : (0 : ℚ)<(hd : ℚ) := by exact_mod_cast hhd
  have he : ((sumFold terms (1,0)).2 : ℚ)/(sumFold terms (1,0)).1=
      (terms.map (fun t => (t.2 : ℚ)/t.1)).sum := by simpa using hh.2
  rw [← he]
  have htgt : (hn : ℚ)/hd*((q : ℚ)+total)=(hn*((q : ℚ)+total))/hd := by ring
  rw [htgt,div_le_div_iff₀ hhD hD]
  have hre : (hn : ℚ)*((q : ℚ)+total)*(sumFold terms (1,0)).1=
      hn*(sumFold terms (1,0)).1*((q : ℚ)+total) := by ring
  rw [hre]
  exact_mod_cast Iff.rfl

/-- A maximum over nonnegative witness numerators removes the quadratic
balance scan without changing the guessed-support condition. -/
theorem balance_max_iff {n : ℕ} (p : Fin n→ℤ) (A : Finset (Fin n)) (αn αd : ℤ)
    (hp : ∀ i,0≤p i) (hoff : ∀ i,i∉A→p i=0) (ha : 0≤αn)
    (m : ℤ) (hm : m ∈ insert 0 (Finset.univ.image p)) (hmax : ∀ i,p i ≤ m) :
    (∀ i∈A,∀ j∈A,αn*p j≤p i*αd) ↔ ∀ i∈A,αn*m≤p i*αd := by
  constructor
  · intro h i hi
    rcases Finset.mem_insert.mp hm with rfl | hm
    · have hmi : p i=0 := le_antisymm (hmax i) (hp i)
      simp [hmi]
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hm
      by_cases hj : j∈A
      · exact h i hi j hj
      · have hz := hoff j hj
        have hmi : p i=0 := le_antisymm (by simpa [hz] using hmax i) (hp i)
        simp [hz,hmi]
  · intro h i hi j hj
    exact (mul_le_mul_of_nonneg_left (hmax j) ha).trans (h i hi)

end BalancedAssortments.DirectVerifier
