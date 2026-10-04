import BalancedAssortments.ComplexityTimeSourceCorrect

/-! Acceptance depends on decoded raw signed bit strings, with no executed
canonicalization of certificates. -/
namespace BalancedAssortments.ComplexityTimeSourcePipeline
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions
open ComplexityTimeSourceRows DecisionPolyhedron

private theorem zip_values (as bs : List ZBits) :
    (as.zip bs).map (fun v => zvalue v.1*zvalue v.2) =
      ((as.map zvalue).zip (bs.map zvalue)).map (fun v => v.1*v.2) := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih => cases bs <;> simp [ih]

theorem rowHolds_value_congr (as p p' : List ZBits) (b q q' : ZBits)
    (hp : p.map zvalue = p'.map zvalue) (hq : zvalue q = zvalue q') :
    RowHolds as p b q ↔ RowHolds as p' b q' := by
  have hl : p.length = p'.length := by simpa using congrArg List.length hp
  simp only [RowHolds, hl, zip_values, hp, hq]

theorem checkSystem_value_congr (p p' : List ZBits) (q q' : ZBits)
    (rows : List (List ZBits × ZBits))
    (hp : p.map zvalue = p'.map zvalue) (hq : zvalue q = zvalue q') :
    (checkSystem p q rows).1 = (checkSystem p' q' rows).1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkSystem_correct, hq]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro row
  exact imp_congr_right (fun _ => rowHolds_value_congr row.1 p p' row.2 q q' hp hq)

def rawCertificateValues {n : ℕ} (p : List ZBits) : Fin n → ℤ :=
  fun i => zvalue (p[i.val]?.getD zzero)

theorem rawCertificateValues_map {n : ℕ} (p : List ZBits) (hp : p.length = n) :
    p.map zvalue = List.ofFn (rawCertificateValues (n := n) p) := by
  apply List.ext_getElem
  · simp [hp]
  · intro i hi hj
    have hip : i < p.length := by simpa using hi
    simp [rawCertificateValues, hip]

/-- Even arbitrary raw certificates must have the correct dimension on
acceptance: the actual row checker enforces it. -/
theorem verifySourceSized_accepted_dimension {n : ℕ} (v r : List Fraction)
    (α H : Fraction) (K mask : List Bool) (p : List ZBits) (q : ZBits)
    (ha : (verifySourceSized n v r α H K mask p q).1 = true) : p.length = n := by
  have hs := (checkSystem_correct p q (compileRows v r α H K mask (rowList n)).1).1 ha
  have hm : (compiledRow v r α H K mask (Row.rank : Row n)).1 ∈
      (compileRows v r α H K mask (rowList n)).1 := by
    rw [compileRows_data]
    exact List.mem_map.mpr ⟨Row.rank, rowList_complete _, rfl⟩
  have hh := (hs.2 _ hm).1
  rw [compiledRow_length] at hh
  exact hh.symm

/-- Complete acceptance characterization for arbitrary signed bit-string
certificates, including noncanonical and padded encodings. -/
theorem verifySourceSized_raw_correct {n : ℕ} (v r : List Fraction) (α H : Fraction)
    (K mask : List Bool)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (p : List ZBits) (q : ZBits) (hp : p.length = n) :
    (verifySourceSized n v r α H K mask p q).1 = true ↔
      0 < zvalue q ∧ (fun j => (rawCertificateValues (n := n) p j : ℝ)/(zvalue q : ℝ)) ∈
        PolyhedralBasis.polyhedron
          (realMatrix (decodedValues v) (decodedValues r) (decode α) (decode H) (support mask n))
          (realBound (decodedValues v) (value K) (decode H)) := by
  have henc : (encodedNumerators (rawCertificateValues (n := n) p)).map zvalue =
      List.ofFn (rawCertificateValues (n := n) p) := by
    simp [encodedNumerators, List.map_ofFn, Function.comp_def]
  have hh := checkSystem_value_congr p (encodedNumerators (rawCertificateValues (n := n) p))
    q (zencode (zvalue q)) (compileRows v r α H K mask (rowList n)).1
    ((rawCertificateValues_map p hp).trans henc.symm) (by simp)
  change (checkSystem p q (compileRows v r α H K mask (rowList n)).1).1 = true ↔ _
  rw [hh]
  exact verifySourceSized_correct v r α H K mask hv hr hα hH _ _

end BalancedAssortments.ComplexityTimeSourcePipeline
