import BalancedAssortments.FixedSupportCostInputSize

namespace BalancedAssortments.FixedSupportCostProgram
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostPoints NPCNF

def fractionFields (x : Fraction) : List (List Bool) := [x.num.1,x.num.2,x.den]
def productFields (p : Product) : List (List Bool) := fractionFields p.1++fractionFields p.2
def productsFields {I : Type*} : List (I×Product) → List (List Bool)
  | [] => []
  | p::ps => productFields p.2++productsFields ps
/-- Coordinates are serialized in their prescribed positional order. The
source label invariant is checked separately by the solver correctness theorem. -/
def inputFields {I : Type*} (α K : Fraction) (ps : List (I×Product)) : List (List Bool) :=
  fractionFields α++fractionFields K++productsFields ps
def serializedInput {I : Type*} (α K : Fraction) (ps : List (I×Product)) : List Bool :=
  Encoding.encodeFields (inputFields α K ps)

lemma fractionFields_size (x : Fraction) :
    ((fractionFields x).map (fun b => 2*b.length+1)).sum=2*fractionVolume x+3 := by
  simp [fractionFields,fractionVolume]
  omega
lemma productsFields_size {I : Type*} (ps : List (I×Product)) :
    ((productsFields ps).map (fun b => 2*b.length+1)).sum=
      6*ps.length+2*(ps.map (fun p => fractionVolume p.2.1+fractionVolume p.2.2)).sum := by
  induction ps with
  | nil => simp [productsFields]
  | cons p ps ih =>
    simp only [productsFields,List.map_append,List.sum_append,productFields,fractionFields_size,ih,
      List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem serializedInput_length {I : Type*} (α K : Fraction) (ps : List (I×Product)) :
    (serializedInput α K ps).length=6+6*ps.length+
      2*(fractionVolume α+fractionVolume K+(ps.map (fun p => fractionVolume p.2.1+fractionVolume p.2.2)).sum) := by
  simp only [serializedInput,Encoding.encodeFields_length,inputFields,List.map_append,List.sum_append,
    fractionFields_size,productsFields_size]
  omega

lemma inputVolume_le_serialized {I : Type*} (α K : Fraction) (ps : List (I×Product)) :
    inputVolume α K ps ≤ (serializedInput α K ps).length := by
  rw [serializedInput_length]
  unfold inputVolume
  omega

/-- The concrete framing is consumed by the already verified actual parser;
there is no unspecified external word-size convention in the size measure. -/
theorem serializedInput_parses {I : Type*} (α K : Fraction) (ps : List (I×Product)) :
    (EncodingTime.parse (serializedInput α K ps)).1=some (inputFields α K ps) :=
  Encoding.parseFields_encode _

/-- Exact-support optimization cost in the length of its self-delimiting
signed-rational encoding. This specializes the same raw program, not a wrapper
that performs uncharged rational normalization or arithmetic. -/
theorem runBits_polynomial_serialized : ∃ P : Polynomial ℕ,∀ {I : Type*}
    (α K : Fraction) (ps : List (I×Product)),Valid α → Valid K → (∀ p∈ps,p.2.Valid) →
      (runBits α K ps).2 ≤ P.eval (serializedInput α K ps).length := by
  obtain ⟨P,hP⟩ := runCost_polynomial
  refine ⟨P,?_⟩
  intro I α K ps ha hk hp
  rw [← hP]
  have hsize := inputVolume_le_serialized α K ps
  exact (runBits_input_cost α K ps ha hk hp).trans
    ((runCost_mono_count ((inputVolume_bounds α K ps).1.trans hsize)).trans
      (runCost_mono_width hsize))

end BalancedAssortments.FixedSupportCostProgram
