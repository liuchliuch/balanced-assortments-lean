import BalancedAssortments.ComplexityTimeSourceValidation

namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeSourcePipeline ComplexityEncoding

/-- Signed records are two unsigned magnitudes, matching the actual checker. -/
def naturalParts (z : ℤ) : ℕ × ℕ := if z<0 then (0,z.natAbs) else (z.natAbs,0)

@[simp] theorem naturalParts_bits (z : ℤ) :
    ((naturalParts z).1.bits,(naturalParts z).2.bits) = zencode z := by
  unfold naturalParts zencode
  split_ifs <;> simp

@[simp] theorem parseMask_standard (b : Bool) : (parseMask b.toNat.bits).1 = some b := by
  cases b <;> norm_num [parseMask,Nat.bits,compareBits,lowCompare] <;> decide

def numeratorFields : List Bool → List ℤ → List ℕ
  | [],[] => []
  | b::bs,p::ps => b.toNat::(naturalParts p).1::(naturalParts p).2::numeratorFields bs ps
  | _,_ => []

def certificateEncoding {n : ℕ} (mask : List Bool) (p : Fin n → ℤ) (q : ℤ) : List Bool :=
  encodeFields ((naturalParts q).1::(naturalParts q).2::numeratorFields mask (List.ofFn p))

theorem parseTriples_encoded (mask : List Bool) (ps : List ℤ) (hlen : mask.length = ps.length) :
    (parseTriples ((numeratorFields mask ps).map Nat.bits)).1 = some (mask,ps.map zencode) := by
  induction mask generalizing ps with
  | nil => cases ps <;> simp_all [numeratorFields,parseTriples]
  | cons b bs ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      have hh := ih ps (by simpa using hlen)
      simp [numeratorFields,parseTriples,parseMask_standard,hh,naturalParts_bits]

/-- Every semantic support/numerator/shared-denominator certificate has an actual
accepted parse. Signed values are preserved exactly, without rational normalization. -/
theorem parseCertificate_encoded {n : ℕ} (mask : List Bool) (p : Fin n → ℤ) (q : ℤ)
    (hlen : mask.length = n) :
    (parseCertificate (certificateEncoding mask p q)).1 =
      some ⟨zencode q,mask,encodedNumerators p⟩ := by
  have hp := EncodingTime.parse_encoded ((naturalParts q).1::(naturalParts q).2::numeratorFields mask (List.ofFn p))
  have ht := parseTriples_encoded mask (List.ofFn p) (by simpa using hlen)
  simp only [certificateEncoding,parseCertificate,hp.1,List.map_cons,packCertificate,ht]
  simp only [naturalParts_bits,Option.map_some,encodedNumerators,List.map_ofFn,Function.comp_def]

theorem pair_field_size (z : ℤ) : (naturalParts z).1.size+(naturalParts z).2.size = z.natAbs.size := by
  unfold naturalParts
  split_ifs <;> simp

theorem numeratorEncoding_length (mask : List Bool) (ps : List ℤ) (C : ℕ)
    (hlen : mask.length = ps.length) (hp : ∀ z ∈ ps, z.natAbs.size ≤ C) :
    (encodeFields (numeratorFields mask ps)).length ≤ ps.length*(2*C+5) := by
  induction mask generalizing ps with
  | nil => cases ps <;> simp_all [numeratorFields,encodeFields]
  | cons b bs ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      have hi := ih ps (by simpa using hlen) (fun z hz => hp z (by simp [hz]))
      have hpp := hp p (by simp)
      have hpair := pair_field_size p
      have hbit : b.toNat.size ≤ 1 := by cases b <;> simp
      simp only [numeratorFields,encodeFields,List.flatMap_cons,List.length_append,encodeNat_length,
        List.length_cons] at ⊢
      unfold encodeFields at hi
      nlinarith

/-- Real wire length for the total parser's certificate grammar. -/
theorem certificateEncoding_short {n C : ℕ} (mask : List Bool) (p : Fin n → ℤ) (q : ℤ)
    (hm : mask.length = n) (hp : ∀ j, (p j).natAbs.size ≤ C) (hq : q.natAbs.size ≤ C) :
    (certificateEncoding mask p q).length ≤ n*(2*C+5)+2*C+2 := by
  have hi := numeratorEncoding_length mask (List.ofFn p) C (by simpa using hm)
    (by simpa only [List.forall_mem_ofFn_iff] using hp)
  have hpair := pair_field_size q
  simp only [List.length_ofFn] at hi
  simp only [certificateEncoding,encodeFields,List.flatMap_cons,List.length_append,encodeNat_length]
  unfold encodeFields at hi
  nlinarith

end BalancedAssortments.ComplexityTimeSourceParsing
