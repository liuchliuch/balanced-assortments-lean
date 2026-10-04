import BalancedAssortments.ComplexityTimeSourceSize
import BalancedAssortments.ComplexityTimeSourceCorrect
import BalancedAssortments.PolyhedralBasisCoefficientBounds
import BalancedAssortments.ComplexityEncoding

/-! Coefficient bounds from actual raw field widths and an explicit serialized
certificate length. The coefficient-size hypotheses are not external oracles. -/
namespace BalancedAssortments.ComplexityTimeSourcePipeline
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open PolyhedralBasis DecisionPolyhedron ComplexityEncoding

lemma bit_value_bound (x : List Bool) (B : ℕ) (h : x.length ≤ B) : value x < 2^B :=
  (Decomposition.CostBinary.value_lt_pow_length x).trans_le (Nat.pow_le_pow_right (by omega) h)

lemma zvalue_abs_bound (x : ZBits) (B : ℕ) (h : ComplexityTimeVerifier.width x ≤ B) :
    |zvalue x| ≤ (2:ℤ)^B := by
  have hp := bit_value_bound x.1 B ((le_max_left _ _).trans h)
  have hn := bit_value_bound x.2 B ((le_max_right _ _).trans h)
  have hp' : (value x.1 : ℤ) < (2:ℤ)^B := by exact_mod_cast hp
  have hn' : (value x.2 : ℤ) < (2:ℤ)^B := by exact_mod_cast hn
  unfold zvalue
  apply abs_le.mpr
  constructor <;> omega

/-- Canonical reduced rational coefficients have no greater magnitudes than the
raw fraction fields. This is a semantic size theorem, not an executed gcd. -/
theorem raw_width_coefficient_bound (x : Fraction) (B : ℕ)
    (hv : Valid x) (hw : ComplexityTimeFractions.width x ≤ B) : CoeffBound B (decode x) := by
  have hn := zvalue_abs_bound x.num B ((le_max_left _ _).trans hw)
  have hd := bit_value_bound x.den B ((le_max_right _ _).trans hw)
  have hdp : (0:ℤ) < value x.den := by exact_mod_cast hv
  have hdb : |(value x.den : ℤ)| ≤ (2:ℤ)^B := by
    rw [abs_of_nonneg hdp.le]
    exact_mod_cast hd.le
  have h := CoeffBound.of_fraction (ne_of_gt hdp) hn hdb
  simpa only [Rat.divInt_eq_div,Int.cast_natCast,decode] using h

/-- Original raw source size, before adding any certificate. -/
def sourceInputSize (v r : List Fraction) (α H : Fraction) (K : List Bool) : ℕ :=
  v.length+r.length+(v.map fractionSize).sum+(r.map fractionSize).sum+
    fractionSize α+fractionSize H+K.length+1

/-- One sign bit followed by the same self-delimiting binary natural field used
elsewhere in the repository. -/
def signedEncoding (z : ℤ) : List Bool := decide (z<0) :: encodeNat z.natAbs

@[simp] theorem signedEncoding_length (z : ℤ) : (signedEncoding z).length = 2*z.natAbs.size+2 := by
  simp [signedEncoding]

def certificateBits {n : ℕ} (mask : List Bool) (p : Fin n → ℤ) (q : ℤ) : List Bool :=
  mask ++ (List.ofFn (fun j => signedEncoding (p j))).flatten ++ signedEncoding q

theorem certificateBits_length {n : ℕ} (mask : List Bool) (p : Fin n → ℤ) (q : ℤ) :
    (certificateBits mask p q).length = mask.length+2*(∑ j, (p j).natAbs.size)+2*n+2*q.natAbs.size+2 := by
  simp [certificateBits,List.length_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def,
    Finset.sum_add_distrib,Finset.mul_sum]
  ring

theorem certificateBits_short {n C : ℕ} (mask : List Bool) (p : Fin n → ℤ) (q : ℤ)
    (hm : mask.length = n) (hp : ∀ j, (p j).natAbs.size ≤ C) (hq : q.natAbs.size ≤ C) :
    (certificateBits mask p q).length ≤ n+(n+1)*(2*C+2) := by
  have hs : (∑ j, (p j).natAbs.size) ≤ n*C := by
    calc (∑ j, (p j).natAbs.size) ≤ ∑ _j : Fin n, C := Finset.sum_le_sum (fun j _ => hp j)
         _ = n*C := by simp
  rw [certificateBits_length,hm]
  nlinarith

@[simp] theorem integerSize_zencode (z : ℤ) : integerSize (zencode z) = z.natAbs.size+1 := by
  unfold zencode
  split_ifs <;> simp [integerSize,Nat.size_eq_bits_len]

/-- The stored-bit metric of the verifier is bounded by the original source
size plus the actual serialized certificate bytes (bits). -/
theorem totalInputSize_le_serialized {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (p : Fin n → ℤ) (q : ℤ) :
    totalInputSize v r α H K mask (encodedNumerators p) (zencode q) ≤
      sourceInputSize v r α H K+(certificateBits mask p q).length := by
  rw [certificateBits_length]
  simp only [totalInputSize,sourceInputSize,encodedNumerators,List.length_ofFn,
    List.map_ofFn,List.sum_ofFn,Function.comp_def,integerSize_zencode,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  omega

def witnessWidth (n B : ℕ) : ℕ := n*((B+B+1)*(n+1)+n)+1

def certificateBound (L : ℕ) : ℕ := L+(L+1)*(2*witnessWidth L L+2)

/-- Endogenous support and all rational numerator/denominator certificate fields
have a uniform polynomial serialized size in the actual original raw input. -/
theorem source_has_short_binary_certificate {n : ℕ}
    (v r : List Fraction) (α H : Fraction) (K : List Bool) (hlen : v.length = n)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (hyes : ∃ x : Fin n → ℝ,
      Sales.CompactFeasible (fun j => (decodedValues v j : ℝ)) x (value K) ∧
      Sales.Balanced (decode α : ℝ) x ∧
      (decode H : ℝ) ≤ Sales.objective (fun j => (decodedValues r j : ℝ)) x) :
    ∃ (mask : List Bool) (p : Fin n → ℤ) (q : ℤ), mask.length = n ∧
      (verifySourceSized n v r α H K mask (encodedNumerators p) (zencode q)).1 = true ∧
      (certificateBits mask p q).length ≤ certificateBound (sourceInputSize v r α H K) := by
  let L := sourceInputSize v r α H K
  have hL : 1 ≤ L := by dsimp [L,sourceInputSize]; omega
  have hn : n ≤ L := by dsimp [L,sourceInputSize]; omega
  have hlookup (xs : List Fraction) (hx : (xs.map fractionSize).sum ≤ L) (i : ℕ) :
      ComplexityTimeFractions.width (lookup zero xs i).1 ≤ L := by
    apply lookup_property (fun f => ComplexityTimeFractions.width f ≤ L) zero xs i
    · simpa using hL
    · intro f hf
      exact (fractionWidth_le_size f).trans ((size_mem_le_sum fractionSize xs f hf).trans hx)
  have bv : ∀ j : Fin n, CoeffBound L (decodedValues v j) := by
    intro j
    apply raw_width_coefficient_bound _ L (hv j).1
    exact hlookup v (by dsimp [L,sourceInputSize]; omega) j.val
  have br : ∀ j : Fin n, CoeffBound L (decodedValues r j) := by
    intro j
    apply raw_width_coefficient_bound _ L (hr j)
    exact hlookup r (by dsimp [L,sourceInputSize]; omega) j.val
  have ba : CoeffBound L (decode α) := raw_width_coefficient_bound α L hα
    ((fractionWidth_le_size α).trans (by dsimp [L,sourceInputSize]; omega))
  have bH : CoeffBound L (decode H) := raw_width_coefficient_bound H L hH
    ((fractionWidth_le_size H).trans (by dsimp [L,sourceInputSize]; omega))
  have bK : CoeffBound L (value K : ℚ) := by
    have hh := raw_width_coefficient_bound (fromNatural K) L (fromNatural_valid K)
      (by rw [fromNatural_width]; dsimp [L,sourceInputSize]; omega)
    simpa using hh
  obtain ⟨mask,p,q,hm,hacc,hq,hp⟩ := verifySourceSized_complete_short v r α H K hv hr hα hH bv br ba bH bK hyes
  refine ⟨mask,p,q,hm,hacc,?_⟩
  have hwidth : witnessWidth n L ≤ witnessWidth L L := by unfold witnessWidth; gcongr
  have hs := certificateBits_short mask p q hm hp hq
  change _ ≤ certificateBound L
  unfold certificateBound
  have hpoly : n+(n+1)*(2*witnessWidth n L+2) ≤ L+(L+1)*(2*witnessWidth L L+2) := by gcongr
  exact hs.trans hpoly

end BalancedAssortments.ComplexityTimeSourcePipeline

namespace BalancedAssortments.ComplexityTimeSourcePipeline
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows

noncomputable def certificatePolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  X+(X+1)*(2*(X*((X+X+1)*(X+1)+X)+1)+2)

theorem certificatePolynomial_eval (L : ℕ) : certificatePolynomial.eval L = certificateBound L := by
  simp [certificatePolynomial,certificateBound,witnessWidth]

noncomputable def verificationTimePolynomial : Polynomial ℕ :=
  sourceTimePolynomial.comp (Polynomial.X+certificatePolynomial)

theorem verificationTimePolynomial_eval (L : ℕ) :
    verificationTimePolynomial.eval L = sourceTimePolynomial.eval (L+certificateBound L) := by
  simp [verificationTimePolynomial,Polynomial.eval_comp,certificatePolynomial_eval]

lemma sourceTimePolynomial_mono {a b : ℕ} (h : a ≤ b) :
    sourceTimePolynomial.eval a ≤ sourceTimePolynomial.eval b := by
  rw [sourceTimePolynomial_eval,sourceTimePolynomial_eval]
  have hh := sourceBudget_mono h h h h
  omega

/-- Actual source yes-instances have polynomial serialized certificates accepted
by the concrete raw-bit verifier within a polynomial of original source size.
This is an explicit verifier theorem in the bit/list cost model, not an imported
or axiomatized assertion of membership in a machine-defined NP class. -/
theorem source_polynomial_certificate_verifier {n : ℕ}
    (v r : List Fraction) (α H : Fraction) (K : List Bool) (hlen : v.length = n)
    (hrlen : r.length ≤ v.length)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (hyes : ∃ x : Fin n → ℝ,
      Sales.CompactFeasible (fun j => (decodedValues v j : ℝ)) x (value K) ∧
      Sales.Balanced (decode α : ℝ) x ∧
      (decode H : ℝ) ≤ Sales.objective (fun j => (decodedValues r j : ℝ)) x) :
    ∃ (mask : List Bool) (p : Fin n → ℤ) (q : ℤ), mask.length = n ∧
      (verifySource v r α H K mask (encodedNumerators p) (zencode q)).1 = true ∧
      (certificateBits mask p q).length ≤ certificatePolynomial.eval (sourceInputSize v r α H K) ∧
      (verifySource v r α H K mask (encodedNumerators p) (zencode q)).2 ≤
        verificationTimePolynomial.eval (sourceInputSize v r α H K) := by
  obtain ⟨mask,p,q,hm,hacc,hsize⟩ := source_has_short_binary_certificate v r α H K hlen hv hr hα hH hyes
  refine ⟨mask,p,q,hm,?_,?_,?_⟩
  · simpa only [verifySource,hlen] using hacc
  · simpa only [certificatePolynomial_eval] using hsize
  · have ht := verifySource_polynomial_cost v r α H K mask (encodedNumerators p) (zencode q)
      hrlen (by omega)
    have hs := totalInputSize_le_serialized v r α H K mask p q
    have htotal : totalInputSize v r α H K mask (encodedNumerators p) (zencode q) ≤
        sourceInputSize v r α H K+certificateBound (sourceInputSize v r α H K) := by omega
    have hmono := sourceTimePolynomial_mono htotal
    rw [verificationTimePolynomial_eval]
    exact ht.trans hmono

end BalancedAssortments.ComplexityTimeSourcePipeline
