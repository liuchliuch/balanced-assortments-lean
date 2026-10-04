import BalancedAssortments.DirectVerifierMaximum

namespace BalancedAssortments.DirectVerifier
open scoped BigOperators
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions

structure WitnessRecord where
  price : Fraction
  attraction : Fraction
  numerator : ZBits
  active : Bool

def zOne : ZBits := ([true],[])
@[simp] lemma zOne_value : zvalue zOne=1 := by norm_num [zOne,zvalue,value]
@[simp] lemma zzero_value : zvalue zzero=0 := by simp [zzero,zvalue,value]

def recordRankTerm (x : WitnessRecord) : SumBits :=
  (x.attraction.num,(zmul x.numerator (x.attraction.den,[])).1)
def recordRevenueTerm (x : WitnessRecord) : SumBits :=
  ((x.price.den,[]),(zmul x.price.num x.numerator).1)

def totalBits (xs : List ZBits) (a : ZBits) : ZBits := xs.foldl (fun a b => (zadd b a).1) a

lemma totalBits_value (xs : List ZBits) (a : ZBits) :
    zvalue (totalBits xs a)=zvalue a+(xs.map zvalue).sum := by
  induction xs generalizing a with
  | nil => simp [totalBits]
  | cons b bs ih =>
    change zvalue (totalBits bs (zadd b a).1)=_
    rw [ih,zadd_value]
    simp only [List.map_cons,List.sum_cons]
    ring

def checkLocal (q αn αd maximum : ZBits) (x : WitnessRecord) : Bool :=
  (zle zzero x.numerator).1 &&
    (zle (zmul (x.attraction.den,[]) x.numerator).1 (zmul x.attraction.num q).1).1 &&
    (if x.active then (zle (zmul αn maximum).1 (zmul αd x.numerator).1).1
     else (zle x.numerator zzero).1)

/-- A reference bit-list checker with exactly the division-free arithmetic
used by the finite-stack body. No decoded number drives a loop. -/
def checkRecords (α H : Fraction) (K : List Bool) (q : ZBits) (xs : List WitnessRecord) : Bool :=
  let rank := (sumFoldBits (xs.map recordRankTerm) (zOne,zzero)).1
  let revenue := (sumFoldBits (xs.map recordRevenueTerm) (zOne,zzero)).1
  let total := totalBits (xs.map WitnessRecord.numerator) zzero
  let maximum := (maxFoldBits (xs.map WitnessRecord.numerator) zzero).1
  xs.all (checkLocal q α.num (α.den,[]) maximum) &&
    (zle rank.2 (zmul (zmul (K,[]) q).1 rank.1).1).1 &&
    (zle (zmul (zmul H.num revenue.1).1 (zadd q total).1).1
      (zmul (H.den,[]) revenue.2).1).1

lemma checkLocal_correct (q αn αd maximum : ZBits) (x : WitnessRecord) :
    checkLocal q αn αd maximum x=true ↔
      0≤zvalue x.numerator ∧
      zvalue x.numerator*(value x.attraction.den : ℤ)≤zvalue q*zvalue x.attraction.num ∧
      (if x.active then zvalue αn*zvalue maximum≤zvalue x.numerator*zvalue αd
       else zvalue x.numerator=0) := by
  have hn (bs : List Bool) : zvalue (bs,[])=(value bs : ℤ) := by simp [zvalue,value]
  cases h : x.active <;>
    simp only [checkLocal,h,Bool.false_eq_true,if_false,if_true,Bool.and_eq_true,
      zle_correct,zmul_value,zzero_value,hn,mul_comm,and_assoc]
  · omega


def vectorRecords {n : ℕ} (v r : Fin n→Fraction) (p : Fin n→ZBits) (mask : Fin n→Bool) : List WitnessRecord :=
  List.ofFn fun i => ⟨r i,v i,p i,mask i⟩

lemma rankFold_value {n : ℕ} (v r : Fin n→Fraction) (p : Fin n→ZBits) (mask : Fin n→Bool) :
    decodeSum (sumFoldBits ((vectorRecords v r p mask).map recordRankTerm) (zOne,zzero)).1 =
      sumFold (rankTerms v (fun i => zvalue (p i))) (1,0) := by
  rw [sumFoldBits_decode]
  simp only [vectorRecords,List.map_ofFn,Function.comp_def,recordRankTerm,decodeSum,zmul_value,zOne_value,zzero_value]
  simp only [zvalue,value,Nat.cast_zero,sub_zero]
  rfl

lemma revenueFold_value {n : ℕ} (v r : Fin n→Fraction) (p : Fin n→ZBits) (mask : Fin n→Bool) :
    decodeSum (sumFoldBits ((vectorRecords v r p mask).map recordRevenueTerm) (zOne,zzero)).1 =
      sumFold (revenueTerms r (fun i => zvalue (p i))) (1,0) := by
  rw [sumFoldBits_decode]
  simp only [vectorRecords,List.map_ofFn,Function.comp_def,recordRevenueTerm,decodeSum,zmul_value,zOne_value,zzero_value]
  simp only [zvalue,value,Nat.cast_zero,sub_zero]
  rfl

theorem checkRecords_correct {n : ℕ} (v r : Fin n→Fraction) (p : Fin n→ZBits) (mask : Fin n→Bool)
    (α H : Fraction) (K : List Bool) (q : ZBits) :
    checkRecords α H K q (vectorRecords v r p mask)=true ↔
      ClearedMax v r α H (value K) (Finset.univ.filter (fun i => mask i)) (fun i => zvalue (p i)) (zvalue q) := by
  have hpn : (vectorRecords v r p mask).map WitnessRecord.numerator=List.ofFn p := by
    simp [vectorRecords,List.map_ofFn,Function.comp_def]
  have hmax : zvalue (maxFoldBits ((vectorRecords v r p mask).map WitnessRecord.numerator) zzero).1=
      witnessMaximum (fun i => zvalue (p i)) := by rw [hpn,maxFoldBits_ofFn]
  have htot : zvalue (totalBits ((vectorRecords v r p mask).map WitnessRecord.numerator) zzero)=∑ i,zvalue (p i) := by
    rw [hpn,totalBits_value]
    simp [List.map_ofFn,List.sum_ofFn]
  have hd := congrArg Prod.fst (rankFold_value v r p mask)
  have hs := congrArg Prod.snd (rankFold_value v r p mask)
  have hrd := congrArg Prod.fst (revenueFold_value v r p mask)
  have hrs := congrArg Prod.snd (revenueFold_value v r p mask)
  dsimp only [decodeSum] at hd hs hrd hrs
  simp only [checkRecords,Bool.and_eq_true,List.all_eq_true,checkLocal_correct,
    zle_correct,zmul_value,zadd_value,hd,hs,hrd,hrs,htot,hmax]
  simp only [vectorRecords,List.forall_mem_ofFn_iff]
  simp only [ClearedMax,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [zvalue,value,Nat.cast_zero,sub_zero]
  constructor
  · rintro ⟨⟨hl,hk⟩,ht⟩
    refine ⟨fun i => ⟨(hl i).1,(hl i).2.1⟩,hk,?_,?_,?_⟩
    · intro i hi
      have hh := (hl i).2.2
      simpa [hi] using hh
    · intro i hi
      have hh := (hl i).2.2
      simpa [hi] using hh
    · nlinarith
  · rintro ⟨hl,hk,ho,hb,ht⟩
    refine ⟨⟨?_,hk⟩,?_⟩
    · intro i
      refine ⟨(hl i).1,(hl i).2,?_⟩
      by_cases hi : mask i=true
      · simpa [hi] using hb i hi
      · simpa [hi] using ho i hi
    · nlinarith

end BalancedAssortments.DirectVerifier
