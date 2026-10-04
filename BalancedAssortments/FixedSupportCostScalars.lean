import BalancedAssortments.FixedSupportCostPoints

namespace BalancedAssortments.FixedSupportCostScalars
open ComplexityTimeFractions (decode Valid width zero one zero_valid one_valid zero_decode one_decode)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints

/-- All reciprocals and their accumulated sum, with each binary operation charged. -/
def inverseSumBits (vs : List Fraction) : Fraction × ℕ :=
  let invs := mapCost reciprocal vs
  let s := sumAcc zero invs.1
  (s.1, invs.2+s.2+4)

theorem inverseSumBits_valid (vs : List Fraction) : Valid (inverseSumBits vs).1 := by
  apply sumAcc_valid _ _ zero_valid
  intro x hx
  rw [mapCost_value] at hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact reciprocal_valid v

theorem inverseSumBits_decode (vs : List Fraction) :
    decode (inverseSumBits vs).1 = (vs.map (fun v => 1 / decode v)).sum := by
  have hv : ∀ x ∈ (mapCost reciprocal vs).1, Valid x := by
    intro x hx
    rw [mapCost_value] at hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact reciprocal_valid v
  change decode (sumAcc zero (mapCost reciprocal vs).1).1 = _
  rw [sumAcc_decode _ _ zero_valid hv]
  simp [mapCost_value, List.map_map, Function.comp_def, reciprocal_decode]

def inverseWidth (n B : ℕ) : ℕ := 1+n*(2*B+2)

def inverseCost (n B : ℕ) : ℕ :=
  (n*(64*B+36)+1) + (n*(4096*(1+n*(2*B+2)+B+1)^2+4)+1)+4

theorem inverseSumBits_width (vs : List Fraction) {B : ℕ}
    (hv : ∀ v ∈ vs, Valid v) (hw : ∀ v ∈ vs, width v ≤ B) :
    width (inverseSumBits vs).1 ≤ inverseWidth vs.length B := by
  have hi : ∀ x ∈ (mapCost reciprocal vs).1, width x ≤ B := by
    intro x hx
    rw [mapCost_value] at hx
    obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hx
    exact (reciprocal_width v (hv v hv')).trans (hw v hv')
  have hs := sumAcc_width zero (mapCost reciprocal vs).1 (by simp : width zero ≤ 1) hi
  simpa [inverseSumBits, inverseWidth] using hs

theorem inverseSumBits_cost (vs : List Fraction) {B : ℕ}
    (hv : ∀ v ∈ vs, Valid v) (hw : ∀ v ∈ vs, width v ≤ B) :
    (inverseSumBits vs).2 ≤ inverseCost vs.length B := by
  have hi : ∀ x ∈ (mapCost reciprocal vs).1, width x ≤ B := by
    intro x hx
    rw [mapCost_value] at hx
    obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hx
    exact (reciprocal_width v (hv v hv')).trans (hw v hv')
  have hm := mapCost_cost reciprocal vs (C := 64*B+32) (fun v hv' =>
    (reciprocal_cost v).trans (by have := hw v hv'; omega))
  have hs := sumAcc_cost zero (mapCost reciprocal vs).1 (by simp : width zero ≤ 1) hi
  simp only [mapCost_length] at hs
  dsimp only [inverseSumBits, inverseCost]
  nlinarith

def scoreBits (p : Product) (ρ : Fraction) : Fraction × ℕ :=
  let d := subtractFresh p.1 ρ
  let s := multiplyFresh d.1 p.2
  (s.1, d.2+s.2+4)

theorem scoreBits_valid (p : Product) (ρ : Fraction) (hp : p.Valid) (hρ : Valid ρ) :
    Valid (scoreBits p ρ).1 := multiplyFresh_valid _ _ (subtractFresh_valid _ _ hp.1 hρ) hp.2

theorem scoreBits_decode (p : Product) (ρ : Fraction) (hp : p.Valid) (hρ : Valid ρ) :
    decode (scoreBits p ρ).1 = (decode p.1-decode ρ)*decode p.2 := by
  simp only [scoreBits, multiplyFresh_decode, subtractFresh_decode _ _ hp.1 hρ]

theorem scoreBits_width (p : Product) (ρ : Fraction) {A B : ℕ}
    (hp : p.Width B) (hρ : width ρ ≤ A) : width (scoreBits p ρ).1 ≤ 2*A+3*B+3 := by
  have hs := multiplyFresh_width (subtractFresh_width hp.1 hρ) hp.2
  dsimp only [scoreBits]
  omega

theorem scoreBits_cost (p : Product) (ρ : Fraction) {A B : ℕ}
    (hp : p.Width B) (hρ : width ρ ≤ A) : (scoreBits p ρ).2 ≤ 32768*(A+B+1)^2 := by
  have hd := subtractFresh_cost hp.1 hρ
  have hs := multiplyFresh_cost (subtractFresh_width hp.1 hρ) hp.2
  have hs' : (multiplyFresh (subtractFresh p.1 ρ).1 p.2).2 ≤ 9216*(A+B+1)^2 := by
    apply hs.trans
    calc
      1024*(B+2*A+2+B+1)^2 ≤ 1024*(3*(A+B+1))^2 := by gcongr; omega
      _ = 9216*(A+B+1)^2 := by ring
  have hbase : 1 ≤ (A+B+1)^2 := one_le_pow₀ (by omega)
  have hd' : (subtractFresh p.1 ρ).2 ≤ 4096*(A+B+1)^2+2 := by simpa [Nat.add_comm] using hd
  dsimp only [scoreBits]
  omega

def capBits (α t v : Fraction) : Fraction × ℕ :=
  let av := multiplyFresh α v
  let up := divideFresh t av.1
  let m := minimum one up.1
  let low := divideFresh t v
  let c := subtractFresh m.1 low.1
  (c.1, av.2+up.2+m.2+low.2+c.2+8)

theorem capBits_valid (α t v : Fraction) (hα : Valid α) (ht : Valid t) (hv : Valid v) :
    Valid (capBits α t v).1 := by
  apply subtractFresh_valid
  · exact minimum_valid _ _ one_valid (divideFresh_valid _ _ ht (multiplyFresh_valid _ _ hα hv))
  · exact divideFresh_valid _ _ ht hv

theorem capBits_decode (α t v : Fraction) (hα : Valid α) (ht : Valid t) (hv : Valid v) :
    decode (capBits α t v).1 = min 1 (decode t/(decode α*decode v))-decode t/decode v := by
  have hup := divideFresh_valid t (multiplyFresh α v).1 ht (multiplyFresh_valid α v hα hv)
  have hm := minimum_valid one _ one_valid hup
  have hl := divideFresh_valid t v ht hv
  simp only [capBits, subtractFresh_decode _ _ hm hl, minimum_decode _ _ one_valid hup,
    divideFresh_decode, multiplyFresh_decode, one_decode]

theorem capBits_width (α t v : Fraction) {A B : ℕ}
    (hα : Valid α) (hv : Valid v) (hαw : width α ≤ B) (htw : width t ≤ A) (hvw : width v ≤ B) :
    width (capBits α t v).1 ≤ 3*A+10*B+7 := by
  have hav := multiplyFresh_width hαw hvw
  have hup := divideFresh_width_valid htw hav (multiplyFresh_valid _ _ hα hv)
  have hmw := minimum_width one (divideFresh t (multiplyFresh α v).1).1
  have hm : width (minimum one (divideFresh t (multiplyFresh α v).1).1).1 ≤ A+6*B+3 := by
    simp only [ComplexityTimeFractions.one_width] at hmw
    omega
  have hl := divideFresh_width_valid htw hvw hv
  have hc := subtractFresh_width hm hl
  dsimp only [capBits]
  omega

def budgetBits (K t : Fraction) (vs : List Fraction) : Fraction × ℕ :=
  let s := inverseSumBits vs
  let m := multiplyFresh t s.1
  let b := subtractFresh K m.1
  (b.1,s.2+m.2+b.2+6)

theorem budgetBits_valid (K t : Fraction) (vs : List Fraction) (hK : Valid K) (ht : Valid t) :
    Valid (budgetBits K t vs).1 :=
  subtractFresh_valid _ _ hK (multiplyFresh_valid _ _ ht (inverseSumBits_valid vs))

theorem budgetBits_decode (K t : Fraction) (vs : List Fraction) (hK : Valid K) (ht : Valid t) :
    decode (budgetBits K t vs).1 = decode K - decode t * (vs.map (fun v => 1/decode v)).sum := by
  simp only [budgetBits, subtractFresh_decode _ _ hK (multiplyFresh_valid _ _ ht (inverseSumBits_valid vs)),
    multiplyFresh_decode, inverseSumBits_decode]

theorem budgetBits_width (K t : Fraction) (vs : List Fraction) {A B : ℕ}
    (hv : ∀ v ∈ vs, Valid v) (hK : width K ≤ B) (ht : width t ≤ A)
    (hw : ∀ v ∈ vs, width v ≤ B) :
    width (budgetBits K t vs).1 ≤ 2*A+B+4*inverseWidth vs.length B+4 := by
  have hs := inverseSumBits_width vs hv hw
  have hm := multiplyFresh_width ht hs
  have hb := subtractFresh_width hK hm
  dsimp only [budgetBits]
  omega

def budgetCost (n A B : ℕ) : ℕ :=
  inverseCost n B + 1024*(A+inverseWidth n B+1)^2 +
    4096*(B+A+2*inverseWidth n B+2)^2 + 8

theorem budgetBits_cost (K t : Fraction) (vs : List Fraction) {A B : ℕ}
    (hv : ∀ v ∈ vs, Valid v) (hK : width K ≤ B) (ht : width t ≤ A)
    (hw : ∀ v ∈ vs, width v ≤ B) :
    (budgetBits K t vs).2 ≤ budgetCost vs.length A B := by
  have hs := inverseSumBits_width vs hv hw
  have hsc := inverseSumBits_cost vs hv hw
  have hm := multiplyFresh_cost ht hs
  have hmw := multiplyFresh_width ht hs
  have hb := subtractFresh_cost hK hmw
  dsimp only [budgetBits, budgetCost]
  nlinarith

/-- One common polynomial budget for all binary rational primitives. -/
def primitiveCost (W : ℕ) : ℕ := 8192*(2*W+2)^2+64*W+64

private theorem mul_uniform_cost (x y : Fraction) {W : ℕ} (hx : width x ≤ W) (hy : width y ≤ W) :
    (multiplyFresh x y).2 ≤ primitiveCost W := by
  have hh := multiplyFresh_cost hx hy
  unfold primitiveCost
  nlinarith
private theorem div_uniform_cost (x y : Fraction) {W : ℕ} (hx : width x ≤ W) (hy : width y ≤ W) :
    (divideFresh x y).2 ≤ primitiveCost W := by
  have hh := divideFresh_cost hx hy
  unfold primitiveCost
  nlinarith
private theorem min_uniform_cost (x y : Fraction) {W : ℕ} (hx : width x ≤ W) (hy : width y ≤ W) :
    (minimum x y).2 ≤ primitiveCost W := by
  have hh := minimum_cost hx hy
  unfold primitiveCost
  nlinarith
private theorem sub_uniform_cost (x y : Fraction) {W : ℕ} (hx : width x ≤ W) (hy : width y ≤ W) :
    (subtractFresh x y).2 ≤ primitiveCost W := by
  have hh := subtractFresh_cost hx hy
  unfold primitiveCost
  nlinarith

def capCost (A B : ℕ) : ℕ := 5*primitiveCost (16*(A+B+1))+8

theorem capBits_cost (α t v : Fraction) {A B : ℕ}
    (hα : Valid α) (hv : Valid v) (hαw : width α ≤ B) (htw : width t ≤ A) (hvw : width v ≤ B) :
    (capBits α t v).2 ≤ capCost A B := by
  let W := 16*(A+B+1)
  have ha : width α ≤ W := by dsimp [W]; omega
  have ht : width t ≤ W := by dsimp [W]; omega
  have hv' : width v ≤ W := by dsimp [W]; omega
  have hone : width one ≤ W := by simp only [ComplexityTimeFractions.one_width]; dsimp [W]; omega
  have havw := multiplyFresh_width hαw hvw
  have hav : width (multiplyFresh α v).1 ≤ W := by dsimp [W]; omega
  have hupw := divideFresh_width_valid htw havw (multiplyFresh_valid _ _ hα hv)
  have hup : width (divideFresh t (multiplyFresh α v).1).1 ≤ W := by dsimp [W]; omega
  have hm : width (minimum one (divideFresh t (multiplyFresh α v).1).1).1 ≤ W :=
    (minimum_width _ _).trans (max_le hone hup)
  have hloww := divideFresh_width_valid htw hvw hv
  have hlow : width (divideFresh t v).1 ≤ W := by dsimp [W]; omega
  have c1 := mul_uniform_cost α v ha hv'
  have c2 := div_uniform_cost t (multiplyFresh α v).1 ht hav
  have c3 := min_uniform_cost one (divideFresh t (multiplyFresh α v).1).1 hone hup
  have c4 := div_uniform_cost t v ht hv'
  have c5 := sub_uniform_cost (minimum one (divideFresh t (multiplyFresh α v).1).1).1
    (divideFresh t v).1 hm hlow
  dsimp only [capBits, capCost]
  change _ ≤ 5*primitiveCost W+8
  omega

end BalancedAssortments.FixedSupportCostScalars
