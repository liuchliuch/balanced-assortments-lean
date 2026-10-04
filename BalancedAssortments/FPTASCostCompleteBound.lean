import BalancedAssortments.FPTASCostComplete

namespace BalancedAssortments.FPTASCostComplete
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram Decomposition.CostMachine

/-- Size facts for the actual binary sparse output, including every mask. -/
theorem sparse_binary_shape (ks : Bits) (nums dens : List Bits) {L : ℕ}
    (hL : bitVolume nums+bitVolume dens ≤ L) :
    let out := binaryGreedyRank ks nums dens
    out.1.length ≤ 4*L+1 ∧ out.2.1.length ≤ nums.length+1 ∧
      ∀ a ∈ out.2.1,a.1.length ≤ 4*L+1 ∧ a.2.length=nums.length := by
  have hd : bitVolume dens ≤ L := by omega
  have hn : ∀ x ∈ nums,x.length ≤ L := by
    intro x hx
    have hh : x.length ≤ bitVolume nums := List.le_sum_of_mem (List.mem_map.mpr ⟨x,hx,rfl⟩)
    omega
  have hD : (productBits dens).1.length ≤ 4*L+1 := by
    have hh := productBits_length dens
    omega
  have hcounts := initialBitsCounts_width dens hd 0 nums hn
  have hwidth := binaryGridAux_width nums.length (value ks) (productBits dens).1
    (initialBitsCounts dens 0 nums).1 hD hcounts
  have hlen := binaryGridAux_length nums.length (value ks) (productBits dens).1
    (initialBitsCounts dens 0 nums).1
  refine ⟨?_,?_,?_⟩
  · simpa only [binaryGreedyRank,binaryGreedy,rankTokens_length] using hD
  · simpa only [binaryGreedyRank,binaryGreedy,rankTokens_length] using hlen
  · simpa only [binaryGreedyRank,binaryGreedy,rankTokens_length,initialBitsCounts_length] using hwidth

private theorem fraction_volume (ms : List Fraction) (M : ℕ)
    (hm : ∀ z ∈ ms,z.Width M) :
    bitVolume (ms.map Fraction.numerator)+bitVolume (ms.map Fraction.denominator) ≤ 2*ms.length*M := by
  induction ms with
  | nil => simp
  | cons z ms ih =>
    have hz := hm z (by simp)
    have hi := ih (fun z hz => hm z (by simp [hz]))
    simp only [List.map_cons,bitVolume_cons,List.length_cons]
    nlinarith [hz.1,hz.2]

/-- A literal polynomial for marginal formation, sparse decomposition and tilt. -/
def finishBudget (n a b k : ℕ) : ℕ :=
  let M := a+2*b
  let L := 2*n*M
  let W := a+b+4*L+1
  n*(256*(a+b+1)^2+12)+1 +
    (8192*(n+1)^2*(L+1)^2+3*n+4*k+2) +
    policyBudget n W (n+1)+2*n+8

def finishWidth (n a b : ℕ) : ℕ :=
  let W := a+b+4*(2*n*(a+2*b))+1
  reverseWidth n W (displayWidth n W)

/-- The complete finishing program is polynomial in actual input bit widths;
no normalization is charged as a constant-time operation. -/
theorem finishPolicy_cost_shape (ks : Bits) (vs ws : List Fraction) {n a b : ℕ}
    (hvl : vs.length=n) (hwl : ws.length=n) (hK : value ks ≤ n)
    (hv : ∀ v ∈ vs,v.Width b) (hw : ∀ w ∈ ws,w.Width a) :
    (finishPolicy ks vs ws).2 ≤ finishBudget n a b ks.length ∧
      (finishPolicy ks vs ws).1.length ≤ n+1 ∧
      ∀ p ∈ (finishPolicy ks vs ws).1,p.1.Width (finishWidth n a b) := by
  let ms := (marginalBits ws vs).1
  let M := a+2*b
  let L := 2*n*M
  let W := a+b+4*L+1
  have hml : ms.length=n := by simp [ms,hwl,hvl]
  have hmw : ∀ z ∈ ms,z.Width M := marginalBits_width ws vs hw hv
  have hvolume : bitVolume (ms.map Fraction.numerator)+bitVolume (ms.map Fraction.denominator) ≤ L := by
    simpa only [hml] using fraction_volume ms M hmw
  let sparse := binaryGreedyRank ks (ms.map Fraction.numerator) (ms.map Fraction.denominator)
  have hsparse := sparse_binary_shape ks (ms.map Fraction.numerator) (ms.map Fraction.denominator) hvolume
  have hspLen : sparse.2.1.length ≤ n+1 := by simpa only [List.length_map,hml] using hsparse.2.1
  have hD : sparse.1.length ≤ W := hsparse.1.trans (by dsimp [W];omega)
  have hmass : ∀ x ∈ sparse.2.1,x.1.length ≤ W :=
    fun x hx => (hsparse.2.2 x hx).1.trans (by dsimp [W];omega)
  have hvW : ∀ x ∈ vs,x.Width W := fun x hx =>
    ⟨(hv x hx).1.trans (by dsimp [W];omega),(hv x hx).2.trans (by dsimp [W];omega)⟩
  have hwW : ∀ x ∈ ws,x.Width W := fun x hx =>
    ⟨(hw x hx).1.trans (by dsimp [W];omega),(hw x hx).2.trans (by dsimp [W];omega)⟩
  have hp0 := policyOutput_cost vs ws sparse.1 sparse.2.1 hvl.le hwl.le hvW hwW hD hmass
  have hp : (policyOutput vs ws sparse.1 sparse.2.1).2 ≤ policyBudget n W (n+1) := by
    apply hp0.trans
    unfold policyBudget
    gcongr
  have hz := marginalBits_cost ws vs hw hv
  rw [hwl] at hz
  have hd := binaryGreedyRank_bit_cost ks (ms.map Fraction.numerator) (ms.map Fraction.denominator)
    (by simp [hml]) (by simp [hml]) hK hvolume
  change sparse.2.2 ≤ 8192*(n+1)^2*(L+1)^2+3*n+4*ks.length+2 at hd
  have hwidth := policyOutput_width vs ws sparse.1 sparse.2.1 hvl.le hwl.le hvW hwW hD hmass
  refine ⟨?_,?_,hwidth⟩
  · change (marginalBits ws vs).2+sparse.2.2+(policyOutput vs ws sparse.1 sparse.2.1).2+2*ms.length+8 ≤ _
    change _ ≤ n*(256*(a+b+1)^2+12)+1 +
      (8192*(n+1)^2*(L+1)^2+3*n+4*ks.length+2)+policyBudget n W (n+1)+2*n+8
    rw [hml]
    omega
  · change (policyOutput vs ws sparse.1 sparse.2.1).1.length ≤ n+1
    rw [policyOutput_length]
    exact hspLen

def runPolicyBudget (b n Q : ℕ) : ℕ :=
  salesBudget b n Q + finishBudget n (salesOutputWidth b n Q) b b + n+6

/-- End-to-end policy running cost is an explicit polynomial in input widths,
product count, and reciprocal requested accuracy. -/
theorem runPolicyBits_cost {n b : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : Bits) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    (hb : 1 ≤ b) (haw : alpha.Width b) (hew : epsilon.Width b) (hkw : ks.length ≤ b)
    (hpw : ∀ i,(rv i).1.Width b ∧ (rv i).2.Width b) :
    (runPolicyBits alpha epsilon ks (sourceProducts rv)).2 ≤
      runPolicyBudget b (n+1) ⌈10/ε⌉₊ := by
  let capacity : Fraction := ⟨ks,[true]⟩
  have hc : capacity.Valid := by norm_num [capacity,Fraction.Valid,value]
  have hcd : capacity.decode=(d.K : ℚ) := by simp [capacity,Fraction.decode,value,hK]
  have hcW : capacity.Width b := ⟨hkw,by simpa [capacity] using hb⟩
  have hpl : (sourceProducts rv).length=n+1 := by simp [sourceProducts]
  have hn : sourceProducts rv ≠ [] := by intro hh; have := congrArg List.length hh; simp [hpl] at this
  have hplist : ∀ p ∈ sourceProducts rv,p.1.Width b ∧ p.2.Width b := by
    intro p hp; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp; exact hpw i
  have hpvalid : ∀ p ∈ sourceProducts rv,p.1.Valid ∧ p.2.Valid := by
    intro p hp; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp; exact hprod i
  have hraw := runSalesBits_analysis alpha epsilon capacity (sourceProducts rv)
    hb haw hew hcW hplist ha he (by rw [hed];exact hε) hpvalid hn
  simp only [hpl,hed] at hraw
  have hsem := runSalesBits_semantics d hd ε hε alpha epsilon capacity rv ha he hc had hed hcd hprod hdec
  let vs := (sourceProducts rv).map Prod.snd
  let ws := (runSalesBits alpha epsilon capacity (sourceProducts rv)).1
  have hvs : vs.length=n+1 := by simp [vs,hpl]
  have hvw : ∀ v ∈ vs,v.Width b := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
    exact (hplist p hp).2
  have hk : value ks ≤ n+1 := by rw [hK];exact hd.2.2.2.2
  have hfinish := finishPolicy_cost_shape ks vs ws hvs hsem.1 hk hvw hraw.2.2
  have hmono : finishBudget (n+1) (salesOutputWidth b (n+1) ⌈10/ε⌉₊) b ks.length ≤
      finishBudget (n+1) (salesOutputWidth b (n+1) ⌈10/ε⌉₊) b b := by
    dsimp only [finishBudget]
    omega
  have hfin := hfinish.1.trans hmono
  change (runSalesBits alpha epsilon capacity (sourceProducts rv)).2+
    (finishPolicy ks vs ws).2+(sourceProducts rv).length+6 ≤ _
  unfold runPolicyBudget
  rw [hpl]
  omega

end BalancedAssortments.FPTASCostComplete
