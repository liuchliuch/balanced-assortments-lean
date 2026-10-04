import BalancedAssortments.FPTASCostCodecParsing
import BalancedAssortments.FPTASCostCodec
import BalancedAssortments.FPTASCostCompletePolynomial

set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
namespace BalancedAssortments.FPTASCostComplete
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram Decomposition.CostMachine

theorem runPolicyBits_width {n b : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    (hb : 1 ≤ b) (haw : alpha.Width b) (hew : epsilon.Width b) (hkw : ks.length ≤ b)
    (hpw : ∀ i,(rv i).1.Width b ∧ (rv i).2.Width b) :
    ∀ p ∈ (runPolicyBits alpha epsilon ks (sourceProducts rv)).1,
      p.1.Width (finishWidth (n+1) (salesOutputWidth b (n+1) ⌈10/ε⌉₊) b) := by
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
  exact hfinish.2.2

end BalancedAssortments.FPTASCostComplete

namespace BalancedAssortments.FPTASCostCodec
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram FPTASCostComplete

def flatWidth (I Q : ℕ) : ℕ := finishWidth I (salesOutputWidth I I Q) I

def flatBudget (I Q : ℕ) : ℕ :=
  100*(I+1)^2+runPolicyBudget I I Q+
    (8*(I+1)+12*((I+1)*(2*flatWidth I Q+I+3))+6)+8

def flatOutputLength (I Q : ℕ) : ℕ := 2*((I+1)*(2*flatWidth I Q+I+3))

lemma outputWidth_mono {b b' n n' q q' : ℕ} (hb : b≤b') (hn : n≤n') (hq : q≤q') :
    salesOutputWidth b n q ≤ salesOutputWidth b' n' q' := by
  dsimp only [salesOutputWidth,FPTASCostGrid.gridWidth,FPTASCostGrid.gridQuota,
    FPTASCostKernel.kernelWidth,FPTASCostOptions.groupWidth]
  gcongr

lemma finishWidth_mono {n n' a a' b b' : ℕ} (hn : n≤n') (ha : a≤a') (hb : b≤b') :
    finishWidth n a b ≤ finishWidth n' a' b' := by
  dsimp only [finishWidth,reverseWidth,displayWidth,sumWidth]
  gcongr

theorem run_bounds_of_inputSize {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    (bits : List Bool)
    (hparse : (parse bits).1 = some ⟨alpha,epsilon,ks,sourceProducts rv⟩)
    (hsize : inputSize alpha epsilon (⟨ks,[true]⟩ : Fraction) (sourceProducts rv) ≤ bits.length) :
    (run bits).2 ≤ flatBudget bits.length ⌈10/ε⌉₊ ∧
      ∃ out, (run bits).1=some out ∧ out.length ≤ flatOutputLength bits.length ⌈10/ε⌉₊ := by
  let I := bits.length
  let ps := (runPolicyBits alpha epsilon ks (sourceProducts rv)).1
  obtain ⟨hb,hN,haw,hew,hkw,hpw⟩ := inputSize_bounds alpha epsilon (⟨ks,[true]⟩ : Fraction) (sourceProducts rv)
  have hNI : n+1 ≤ I := by simpa [sourceProducts,I] using hN.trans hsize
  have hbw : 1 ≤ I := hb.trans hsize
  have aw : alpha.Width I := ⟨haw.1.trans hsize,haw.2.trans hsize⟩
  have ew : epsilon.Width I := ⟨hew.1.trans hsize,hew.2.trans hsize⟩
  have kw : ks.length ≤ I := hkw.1.trans hsize
  have pw : ∀ i,(rv i).1.Width I ∧ (rv i).2.Width I := by
    intro i
    have hh := hpw (rv i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    exact ⟨⟨hh.1.1.trans hsize,hh.1.2.trans hsize⟩,⟨hh.2.1.trans hsize,hh.2.2.trans hsize⟩⟩
  have hc := runPolicyBits_cost d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec hbw aw ew kw pw
  have hc' := hc.trans (runPolicyBudget_mono le_rfl hNI le_rfl)
  have hw := runPolicyBits_width d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec hbw aw ew kw pw
  have hm := runPolicyBits_raw_shape d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec
  have hl := (runPolicyBits_semantics d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec).2.2
  have hl' : ps.length ≤ I+1 := by dsimp [ps]; omega
  have hw' : ∀ p ∈ ps,p.1.Width (flatWidth I ⌈10/ε⌉₊) ∧ p.2.length ≤ I := by
    intro p hp
    have h := hw p hp
    have hmono : finishWidth (n+1) (salesOutputWidth I (n+1) ⌈10/ε⌉₊) I ≤ flatWidth I ⌈10/ε⌉₊ :=
      finishWidth_mono hNI (outputWidth_mono le_rfl hNI le_rfl) le_rfl
    exact ⟨⟨h.1.trans hmono,h.2.trans hmono⟩,by rw [(hm p hp).2];exact hNI⟩
  have hec := emitPolicy_cost ps hw'
  have hel := emitPolicy_length ps hw'
  have hec' : (emitPolicy ps).2 ≤ 8*(I+1)+12*((I+1)*(2*flatWidth I ⌈10/ε⌉₊+I+3))+6 := by
    apply hec.trans
    gcongr
  have hel' : (emitPolicy ps).1.length ≤ flatOutputLength I ⌈10/ε⌉₊ := by
    apply hel.trans
    unfold flatOutputLength
    gcongr
  have hpc := parse_cost bits
  constructor
  · simp only [run,hparse]
    change (parse bits).2+(runPolicyBits alpha epsilon ks (sourceProducts rv)).2+(emitPolicy ps).2+8 ≤ _
    dsimp only [flatBudget]
    dsimp only [I] at hc' hec'
    omega
  · exact ⟨(emitPolicy ps).1,by simp [run,hparse,ps],hel'⟩

theorem run_bounds {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    (bits : List Bool)
    (hparse : (parse bits).1 = some ⟨alpha,epsilon,ks,sourceProducts rv⟩) :
    (run bits).2 ≤ flatBudget bits.length ⌈10/ε⌉₊ ∧
      ∃ out, (run bits).1=some out ∧ out.length ≤ flatOutputLength bits.length ⌈10/ε⌉₊ := by
  exact run_bounds_of_inputSize d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec
    bits hparse (parse_inputSize bits _ hparse)

end BalancedAssortments.FPTASCostCodec
