import BalancedAssortments.NPStackSourcePairingLoop
import BalancedAssortments.ComplexityTimeSourceParsing

namespace BalancedAssortments.NPStackSourcePairing
open ComplexityTimeSourceParsing
open ComplexityTimeFractions (Fraction)

def productRecord (s : Fin 6 → List Bool) : Fraction × Fraction :=
  (⟨(s 0,s 1),s 2⟩,⟨(s 3,s 4),s 5⟩)

lemma parseProducts_records (records : List PairRecord) :
    (parseProducts (records.flatMap (fun r => List.ofFn r.1))).1=
      some (records.map (fun r => productRecord r.1)) := by
  induction records with
  | nil => rfl
  | cons r rs ih => simpa [parseProducts,productRecord] using congrArg (Option.map (fun xs => productRecord r.1::xs)) ih

lemma parseProducts_record_count (records : List PairRecord) :
    (records.map (fun r => productRecord r.1)).length=records.length := by simp

/-- The triple masks keep their raw bit representations. Padded encodings are
accepted exactly when the original source parser accepts them. -/
def MaskRecords (records : List PairRecord) (mask : List Bool) : Prop :=
  List.Forall₂ (fun r b => (parseMask (r.2 0)).1=some b) records mask

lemma parseTriples_records (records : List PairRecord) (mask : List Bool) (h : MaskRecords records mask) :
    (parseTriples (records.flatMap (fun r => List.ofFn r.2))).1=
      some (mask,records.map (fun r => (r.2 1,r.2 2))) := by
  induction h with
  | nil => rfl
  | @cons r b rs bs hr htail ih =>
    change (parseTriples (rs.flatMap (fun r => [r.2 0,r.2 1,r.2 2]))).1=some (bs,rs.map (fun r => (r.2 1,r.2 2))) at ih
    simp only [List.flatMap_cons,List.ofFn_succ,List.ofFn_zero,List.cons_append,List.nil_append,List.map_cons]
    simp [parseTriples,hr,ih]

lemma equal_record_dimensions (records : List PairRecord) (mask : List Bool) (h : MaskRecords records mask) :
    (records.map (fun r => productRecord r.1)).length=mask.length ∧
      (records.map (fun r => (r.2 1,r.2 2))).length=mask.length := by
  have hh := List.Forall₂.length_eq h
  simp [hh]

end BalancedAssortments.NPStackSourcePairing
