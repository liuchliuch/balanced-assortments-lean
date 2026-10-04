import BalancedAssortments.DirectVerifierChecker

namespace BalancedAssortments.DirectVerifier
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions

structure StreamState where
  rank : SumBits
  revenue : SumBits
  total : ZBits
  maximum : ZBits

def streamInitial : StreamState := ⟨(zOne,zzero),(zOne,zzero),zzero,zzero⟩
def streamStep (a : StreamState) (x : WitnessRecord) : StreamState :=
  ⟨(sumStepBits a.rank (recordRankTerm x)).1,
   (sumStepBits a.revenue (recordRevenueTerm x)).1,
   (zadd x.numerator a.total).1,(maxBits a.maximum x.numerator).1⟩
def streamFold : List WitnessRecord→StreamState→StreamState
  | [],a => a
  | x::xs,a => streamFold xs (streamStep a x)

lemma streamFold_rank (xs : List WitnessRecord) (a : StreamState) :
    (streamFold xs a).rank=(sumFoldBits (xs.map recordRankTerm) a.rank).1 := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [streamFold,List.map_cons,sumFoldBits,streamStep] using ih (streamStep a x)
lemma streamFold_revenue (xs : List WitnessRecord) (a : StreamState) :
    (streamFold xs a).revenue=(sumFoldBits (xs.map recordRevenueTerm) a.revenue).1 := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [streamFold,List.map_cons,sumFoldBits,streamStep] using ih (streamStep a x)
lemma streamFold_total (xs : List WitnessRecord) (a : StreamState) :
    (streamFold xs a).total=totalBits (xs.map WitnessRecord.numerator) a.total := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [streamFold,List.map_cons,totalBits,List.foldl_cons,streamStep] using ih (streamStep a x)
lemma streamFold_maximum (xs : List WitnessRecord) (a : StreamState) :
    (streamFold xs a).maximum=(maxFoldBits (xs.map WitnessRecord.numerator) a.maximum).1 := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [streamFold,List.map_cons,maxFoldBits,streamStep] using ih (streamStep a x)

def checkBasic (q : ZBits) (x : WitnessRecord) : Bool :=
  (zle zzero x.numerator).1 &&
    (zle (zmul (x.attraction.den,[]) x.numerator).1 (zmul x.attraction.num q).1).1 &&
    (if x.active then true else (zle x.numerator zzero).1)
def checkBalance (αn αd maximum : ZBits) (x : WitnessRecord) : Bool :=
  if x.active then (zle (zmul αn maximum).1 (zmul αd x.numerator).1).1 else true

def checkFinal (α H : Fraction) (K : List Bool) (q : ZBits) (a : StreamState) : Bool :=
  (zle a.rank.2 (zmul (zmul (K,[]) q).1 a.rank.1).1).1 &&
    (zle (zmul (zmul H.num a.revenue.1).1 (zadd q a.total).1).1
      (zmul (H.den,[]) a.revenue.2).1).1

def streamCheck (α H : Fraction) (K : List Bool) (q : ZBits) (xs : List WitnessRecord) : Bool :=
  let a := streamFold xs streamInitial
  xs.all (checkBasic q) && checkFinal α H K q a && xs.all (checkBalance α.num (α.den,[]) a.maximum)

lemma checkLocal_split (q αn αd maximum : ZBits) (x : WitnessRecord) :
    checkLocal q αn αd maximum x= (checkBasic q x && checkBalance αn αd maximum x) := by
  cases h : x.active <;> simp [checkLocal,checkBasic,checkBalance,h,Bool.and_assoc]

/-- Two structural passes implement exactly the reference checker. The first
pass checks local bounds and accumulates; the second only reads mask/numerators
and checks balance against the recorded maximum. -/
theorem streamCheck_eq (α H : Fraction) (K : List Bool) (q : ZBits) (xs : List WitnessRecord) :
    streamCheck α H K q xs=checkRecords α H K q xs := by
  apply Bool.eq_iff_iff.mpr
  simp only [streamCheck,checkFinal,checkRecords,streamFold_rank,streamFold_revenue,streamFold_total,
    streamFold_maximum,streamInitial,Bool.and_eq_true,List.all_eq_true,checkLocal_split]
  constructor
  · rintro ⟨⟨hb,hr,ht⟩,hbal⟩
    exact ⟨⟨fun x hx => ⟨hb x hx,hbal x hx⟩,hr⟩,ht⟩
  · rintro ⟨⟨hb,hr⟩,ht⟩
    exact ⟨⟨fun x hx => (hb x hx).1,hr,ht⟩,fun x hx => (hb x hx).2⟩

def recordWidth (x : WitnessRecord) : ℕ :=
  max (ComplexityTimeFractions.width x.price) (max (ComplexityTimeFractions.width x.attraction) (width x.numerator))
def streamWidth (a : StreamState) : ℕ :=
  max (sumWidth a.rank) (max (sumWidth a.revenue) (max (width a.total) (width a.maximum)))

lemma recordTerms_width (x : WitnessRecord) {B : ℕ} (hx : recordWidth x≤B) :
    sumWidth (recordRankTerm x)≤3*B+1 ∧ sumWidth (recordRevenueTerm x)≤3*B+1 := by
  have hn : width x.numerator≤B := by unfold recordWidth at hx;omega
  have hv : width x.attraction.num≤B := by unfold recordWidth ComplexityTimeFractions.width at hx;omega
  have hvd : x.attraction.den.length≤B := by unfold recordWidth ComplexityTimeFractions.width at hx;omega
  have hr : width x.price.num≤B := by unfold recordWidth ComplexityTimeFractions.width at hx;omega
  have hrd : x.price.den.length≤B := by unfold recordWidth ComplexityTimeFractions.width at hx;omega
  have hvdw : ComplexityTimeVerifier.width (x.attraction.den,[])≤B := by
    simpa [ComplexityTimeVerifier.width] using hvd
  have hrdw : ComplexityTimeVerifier.width (x.price.den,[])≤B := by
    simpa [ComplexityTimeVerifier.width] using hrd
  have h1 := zmul_width x.numerator (x.attraction.den,[])
  have h2 := zmul_width x.price.num x.numerator
  dsimp only [recordRankTerm,recordRevenueTerm,sumWidth]
  constructor
  · apply max_le <;> omega
  · apply max_le <;> omega

lemma streamStep_width (a : StreamState) (x : WitnessRecord) {A B : ℕ}
    (ha : streamWidth a≤A) (hx : recordWidth x≤B) :
    streamWidth (streamStep a x)≤A+6*B+4 := by
  have har : sumWidth a.rank≤A := by unfold streamWidth at ha;omega
  have hav : sumWidth a.revenue≤A := by unfold streamWidth at ha;omega
  have hat : width a.total≤A := by unfold streamWidth at ha;omega
  have ham : width a.maximum≤A := by unfold streamWidth at ha;omega
  have hp : width x.numerator≤B := by unfold recordWidth at hx;omega
  have hw := recordTerms_width x hx
  have hr := sumStepBits_width a.rank (recordRankTerm x) har hw.1
  have hv := sumStepBits_width a.revenue (recordRevenueTerm x) hav hw.2
  have ht := zadd_width x.numerator a.total
  have hm := maxBits_width a.maximum x.numerator
  dsimp only [streamWidth,streamStep]
  omega

theorem streamFold_width (xs : List WitnessRecord) (a : StreamState) {A B : ℕ}
    (ha : streamWidth a≤A) (hx : ∀ x∈xs,recordWidth x≤B) :
    streamWidth (streamFold xs a)≤A+xs.length*(6*B+4) := by
  induction xs generalizing a A with
  | nil => simpa [streamFold] using ha
  | cons x xs ih =>
    have hh := ih (streamStep a x) (streamStep_width a x ha (hx x (by simp))) (fun y hy => hx y (by simp [hy]))
    simp only [streamFold,List.length_cons]
    nlinarith

end BalancedAssortments.DirectVerifier
