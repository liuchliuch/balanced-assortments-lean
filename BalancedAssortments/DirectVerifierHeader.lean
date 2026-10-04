import BalancedAssortments.DirectVerifierSource
import BalancedAssortments.DirectVerifierStream

namespace BalancedAssortments.DirectVerifier
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions
open ComplexityTimeSourceParsing

def unsigned (xs : List Bool) : ZBits := (xs,[])
@[simp] lemma unsigned_value (xs : List Bool) : zvalue (unsigned xs)=(value xs : ℤ) := by simp [unsigned,zvalue,value]

def positive (x : ZBits) : Bool := !(zle x zzero).1
lemma positive_correct (x : ZBits) : positive x=true ↔ 0<zvalue x := by
  have hh := zle_correct x zzero
  simp only [zzero_value] at hh
  cases he : (zle x zzero).1 <;> simp_all [positive]

def headerGuard (s : Source) (q count : ZBits) : Bool :=
  (zle (unsigned s.declaredCount) count).1 && (zle count (unsigned s.declaredCount)).1 &&
  positive count && positive (unsigned s.capacity) && (zle (unsigned s.capacity) count).1 &&
  positive s.alpha.num && positive (unsigned s.alpha.den) &&
  (zle s.alpha.num (unsigned s.alpha.den)).1 && positive (unsigned s.target.den) && positive q

def HeaderLegal (s : Source) (q : ZBits) : Prop :=
  value s.declaredCount=s.products.length ∧ 0<s.products.length ∧
  0<value s.capacity ∧ value s.capacity≤s.products.length ∧
  (Valid s.alpha ∧ 0<decode s.alpha) ∧ decode s.alpha≤1 ∧ Valid s.target ∧ 0<zvalue q

lemma headerGuard_correct (s : Source) (q count : ZBits)
    (hc : zvalue count=(s.products.length : ℤ)) :
    headerGuard s q count=true ↔ HeaderLegal s q := by
  have ha : (0<zvalue s.alpha.num ∧ 0<value s.alpha.den) ↔ Valid s.alpha ∧ 0<decode s.alpha := by
    have hh := fractionPositive_correct s.alpha
    simp only [fractionPositive,Bool.and_eq_true,bitsPositive_correct,integerPositive_correct] at hh
    exact and_comm.trans hh
  have hau (hd : Valid s.alpha) : zvalue s.alpha.num≤(value s.alpha.den : ℤ) ↔ decode s.alpha≤1 := by
    exact (zle_correct s.alpha.num (unsigned s.alpha.den)).symm.trans (by
      simpa [alphaUpper,unsigned] using alphaUpper_correct s.alpha hd)
  simp only [headerGuard,Bool.and_eq_true,zle_correct,unsigned_value,positive_correct,hc]
  unfold HeaderLegal Valid
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨hd1,hd2⟩,hn⟩,hk⟩,hkn⟩,han⟩,had⟩,hau'⟩,hH⟩,hq⟩
    have had' : 0<value s.alpha.den := by exact_mod_cast had
    refine ⟨by omega,by exact_mod_cast hn,by exact_mod_cast hk,by exact_mod_cast hkn,
      ha.mp ⟨han,had'⟩,(hau had').mp hau',by exact_mod_cast hH,hq⟩
  · rintro ⟨hd,hn,hk,hkn,ha',hau',hH,hq⟩
    have hapos := ha.mpr ha'
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨by omega,by omega⟩,?_⟩,?_⟩,?_⟩,hapos.1⟩,?_⟩,(hau ha'.1).mpr hau'⟩,?_⟩,hq⟩
    · exact_mod_cast hn
    · exact_mod_cast hk
    · exact_mod_cast hkn
    · exact_mod_cast ha'.1
    · exact_mod_cast hH

def recordLegal (x : WitnessRecord) : Bool :=
  positive (unsigned x.price.den) && positive x.price.num &&
  positive (unsigned x.attraction.den) && positive x.attraction.num

lemma recordLegal_correct (x : WitnessRecord) : recordLegal x=true ↔
    (Valid x.price ∧ 0<decode x.price) ∧ (Valid x.attraction ∧ 0<decode x.attraction) := by
  have hp := fractionPositive_correct x.price
  have hv := fractionPositive_correct x.attraction
  simp only [fractionPositive,Bool.and_eq_true,bitsPositive_correct,integerPositive_correct] at hp hv
  simp only [recordLegal,Bool.and_eq_true,positive_correct,unsigned_value]
  have hpd : (0 : ℤ)<value x.price.den ↔ 0<value x.price.den := by exact_mod_cast Iff.rfl
  have hvd : (0 : ℤ)<value x.attraction.den ↔ 0<value x.attraction.den := by exact_mod_cast Iff.rfl
  rw [hpd,hvd]
  simpa only [and_assoc] using and_congr hp hv

def countRecordBits (xs : List WitnessRecord) : ZBits := totalBits (xs.map (fun _ => zOne)) zzero
lemma countRecordBits_value (xs : List WitnessRecord) : zvalue (countRecordBits xs)=(xs.length : ℤ) := by
  rw [countRecordBits,totalBits_value]
  simp [List.map_map,Function.comp_def]

end BalancedAssortments.DirectVerifier
