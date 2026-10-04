import BalancedAssortments.DirectVerifierHomogeneous

namespace BalancedAssortments.DirectVerifier
open scoped BigOperators
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions

def rankTerms {n : ℕ} (v : Fin n→Fraction) (p : Fin n→ℤ) : List (ℤ×ℤ) :=
  List.ofFn fun i => (zvalue (v i).num,p i*(value (v i).den : ℤ))
def revenueTerms {n : ℕ} (r : Fin n→Fraction) (p : Fin n→ℤ) : List (ℤ×ℤ) :=
  List.ofFn fun i => ((value (r i).den : ℤ),zvalue (r i).num*p i)

lemma numerator_positive (x : Fraction) (hv : Valid x) (hx : 0<decode x) : 0<zvalue x.num := by
  have hd : (0 : ℚ)<value x.den := by exact_mod_cast hv
  have hh := (div_pos_iff_of_pos_right hd).mp hx
  exact_mod_cast hh

lemma rankTerms_positive {n : ℕ} (v : Fin n→Fraction) (p : Fin n→ℤ)
    (hv : ∀ i,Valid (v i) ∧ 0<decode (v i)) : ∀ t∈rankTerms v p,0<t.1 := by
  intro t ht
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact numerator_positive (v i) (hv i).1 (hv i).2

lemma revenueTerms_positive {n : ℕ} (r : Fin n→Fraction) (p : Fin n→ℤ)
    (hr : ∀ i,Valid (r i)) : ∀ t∈revenueTerms r p,0<t.1 := by
  intro t ht
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  change (0 : ℤ)<(value (r i).den : ℤ)
  exact_mod_cast hr i

lemma rankTerms_sum {n : ℕ} (v : Fin n→Fraction) (p : Fin n→ℤ) :
    ((rankTerms v p).map (fun t => (t.2 : ℚ)/t.1)).sum=∑ i,(p i : ℚ)/decode (v i) := by
  simp only [rankTerms,List.map_ofFn,List.sum_ofFn,Function.comp_def,decode,Int.cast_mul,Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_div_eq_mul_div]

lemma revenueTerms_sum {n : ℕ} (r : Fin n→Fraction) (p : Fin n→ℤ) :
    ((revenueTerms r p).map (fun t => (t.2 : ℚ)/t.1)).sum=∑ i,decode (r i)*(p i : ℚ) := by
  simp only [revenueTerms,List.map_ofFn,List.sum_ofFn,Function.comp_def,decode,Int.cast_mul,Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The integer comparisons made after the streaming accumulation. -/
def Cleared {n : ℕ} (v r : Fin n→Fraction) (α H : Fraction) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n→ℤ) (q : ℤ) : Prop :=
  (∀ i,0≤p i ∧ p i*(value (v i).den : ℤ)≤q*zvalue (v i).num) ∧
  (sumFold (rankTerms v p) (1,0)).2≤(K : ℤ)*q*(sumFold (rankTerms v p) (1,0)).1 ∧
  (∀ i,i∉A→p i=0) ∧
  (∀ i∈A,∀ j∈A,zvalue α.num*p j≤p i*(value α.den : ℤ)) ∧
  zvalue H.num*(sumFold (revenueTerms r p) (1,0)).1*(q+∑ i,p i)≤
    (sumFold (revenueTerms r p) (1,0)).2*(value H.den : ℤ)

theorem cleared_iff_homogeneous {n : ℕ} (v r : Fin n→Fraction) (α H : Fraction) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n→ℤ) (q : ℤ)
    (hv : ∀ i,Valid (v i) ∧ 0<decode (v i)) (hr : ∀ i,Valid (r i))
    (hα : Valid α) (hH : Valid H) :
    Cleared v r α H K A p q ↔
      Homogeneous (fun i => decode (v i)) (fun i => decode (r i)) (decode α) (decode H) K A p q := by
  have hcap (i : Fin n) : p i*(value (v i).den : ℤ)≤q*zvalue (v i).num ↔
      (p i : ℚ)≤q*decode (v i) := by
    have hd : (0 : ℚ)<value (v i).den := by exact_mod_cast (hv i).1
    unfold decode
    rw [← mul_div_assoc,le_div_iff₀ hd]
    exact_mod_cast Iff.rfl
  have hbalance (i j : Fin n) : zvalue α.num*p j≤p i*(value α.den : ℤ) ↔
      decode α*(p j : ℚ)≤p i := by
    have hd : (0 : ℚ)<value α.den := by exact_mod_cast hα
    unfold decode
    rw [div_mul_eq_mul_div,div_le_iff₀ hd]
    exact_mod_cast Iff.rfl
  have hrank := sumFold_bound_iff (rankTerms v p) (rankTerms_positive v p hv) ((K : ℤ)*q)
  rw [rankTerms_sum] at hrank
  have hrev := revenue_cleared_iff (revenueTerms r p) (revenueTerms_positive r p hr)
    q (∑ i,p i) (zvalue H.num) (value H.den) (by exact_mod_cast hH)
  rw [revenueTerms_sum] at hrev
  simp only [Int.cast_mul,Int.cast_natCast,Int.cast_sum] at hrank hrev
  unfold Cleared Homogeneous
  simp only [hcap,hbalance,hrank,hrev,decode]

theorem cleared_iff_source_rows {n : ℕ} (v r : Fin n→Fraction) (α H : Fraction) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n→ℤ) (q : ℤ) (hq : 0<q)
    (hv : ∀ i,Valid (v i) ∧ 0<decode (v i)) (hr : ∀ i,Valid (r i))
    (hα : Valid α) (hH : Valid H) :
    Cleared v r α H K A p q ↔
      (fun i => (p i : ℝ)/(q : ℝ)) ∈ PolyhedralBasis.polyhedron
        (DecisionPolyhedron.realMatrix (fun i => decode (v i)) (fun i => decode (r i)) (decode α) (decode H) A)
        (DecisionPolyhedron.realBound (fun i => decode (v i)) K (decode H)) := by
  rw [DecisionPolyhedron.rows_iff,cleared_iff_homogeneous _ _ _ _ _ _ _ _ hv hr hα hH,
    homogeneous_iff_linear _ _ _ _ _ _ _ _ hq]

end BalancedAssortments.DirectVerifier
