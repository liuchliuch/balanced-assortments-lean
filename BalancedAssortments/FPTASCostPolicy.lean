import BalancedAssortments.FPTASCostOutput
import BalancedAssortments.DecompositionCostRaw
import BalancedAssortments.FPTASPolicy

namespace BalancedAssortments.FPTASCostPolicy
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput
open Decomposition.CostMachine

def normalizer (ws : List Fraction) : Fraction × ℕ :=
  let s := sumFractions ws
  let d := add s.1 one
  (d.1,s.2+d.2+4)

theorem normalizer_decode (ws : List Fraction) (hw : ∀ w ∈ ws, w.Valid) :
    (normalizer ws).1.decode = 1+(ws.map Fraction.decode).sum := by
  simp only [normalizer,add_decode (sumFractions_valid ws hw) one_valid,
    sumFractions_decode ws hw,one_decode]
  ring

theorem normalizer_positive (ws : List Fraction) (hw : ∀ w ∈ ws, w.Valid) :
    0 < (normalizer ws).1.decode := by
  rw [normalizer_decode ws hw]
  have hh : 0 ≤ (ws.map Fraction.decode).sum := List.sum_nonneg (by
    intro x hx; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx; exact decode_nonnegative a)
  linarith

theorem normalizer_width (ws : List Fraction) {n b : ℕ} (hn : ws.length ≤ n)
    (hw : ∀ w ∈ ws, w.Width b) : (normalizer ws).1.Width (displayWidth n b) := by
  simpa [normalizer,displayWidth] using add_width (sumFractions_width_bounded ws hn hw) one_width

def normalizerBudget (n b : ℕ) : ℕ := sumBudget n b+256*(sumWidth n b+2)^2+4

theorem normalizer_cost (ws : List Fraction) {n b : ℕ} (hn : ws.length ≤ n)
    (hw : ∀ w ∈ ws, w.Width b) : (normalizer ws).2 ≤ normalizerBudget n b := by
  have cs := sumFractions_cost_bounded ws hn hw
  have ca := add_cost (sumFractions_width_bounded ws hn hw) one_width
  dsimp only [normalizer,normalizerBudget]
  norm_num only [Nat.add_assoc] at ca ⊢
  omega

def liftAtoms (D : Bits) : List BitAtom → List PolicyAtom × ℕ
  | [] => ([],1)
  | a::as =>
      let tail := liftAtoms D as
      ((⟨a.1,D⟩,a.2)::tail.1,tail.2+4)

lemma liftAtoms_map (D : Bits) (as : List BitAtom) :
    (liftAtoms D as).1 = as.map (fun a => ((⟨a.1,D⟩ : Fraction),a.2)) := by
  induction as <;> simp [liftAtoms, *]

lemma liftAtoms_cost (D : Bits) (as : List BitAtom) : (liftAtoms D as).2 = 4*as.length+1 := by
  induction as <;> simp [liftAtoms, *] <;> omega

/-- Raw binary sparse output followed by exact rational reverse denominator tilt. -/
def policyOutput (vs ws : List Fraction) (D : Bits) (as : List BitAtom) : List PolicyAtom × ℕ :=
  let den := normalizer ws
  let masses := liftAtoms D as
  let out := tiltAtoms vs den.1 masses.1
  (out.1,den.2+masses.2+out.2+8)

lemma chosen_sublist {I : Type*} (ids : List I) (ms : List Bool) :
    (chosen ids ms).Sublist ids := by
  induction ids generalizing ms with
  | nil => simp [chosen]
  | cons i ids ih =>
    cases ms with
    | nil => simp [chosen]
    | cons b bs =>
      cases b
      · exact List.Sublist.cons i (ih bs)
      · exact List.Sublist.cons₂ i (ih bs)

lemma selectFractions_chosen (xs : List Fraction) (ms : List Bool) :
    (selectFractions xs ms).1 = chosen xs ms := by
  induction xs generalizing ms with
  | nil => simp [selectFractions,chosen]
  | cons x xs ih =>
    cases ms with
    | nil =>
      have he : chosen xs [] = [] := by cases xs <;> rfl
      simp [selectFractions,chosen,ih,he]
    | cons b bs => cases b <;> simp [selectFractions,chosen,ih]

lemma mask_sum_finite {n : ℕ} (vs : Fin n → Fraction) (ms : List Bool) :
    (((List.ofFn vs).zip ms).filter (fun p => p.2) |>.map (fun p => p.1.decode)).sum =
      ∑ i ∈ maskSet (n := n) ms, (vs i).decode := by
  rw [← selectFractions_decode (List.ofFn vs) ms,selectFractions_chosen,List.ofFn_eq_map,
    chosen_map,List.map_map,maskSet_eq_chosen]
  rw [List.sum_toFinset _ ((chosen_sublist (List.finRange n) ms).nodup (List.nodup_finRange n))]
  rfl

def interpretPolicy {n : ℕ} (as : List PolicyAtom) : List (Decomposition.Atom n) :=
  as.map fun a => (a.1.decode,maskSet a.2)

/-- Exact list-level equality to the already-certified reverse-tilt policy map. -/
theorem policyOutput_decode {n : ℕ} (vs ws : Fin n → Fraction) (D : Bits) (as : List BitAtom)
    (hv : ∀ i, (vs i).Valid) (hw : ∀ i, (ws i).Valid) :
    interpretPolicy (n := n) (policyOutput (List.ofFn vs) (List.ofFn ws) D as).1 =
      (Decomposition.interpretGrid (value D) (interpretBitAtoms (n := n) as)).map
      (fun a => (a.1*(1+∑ i ∈ a.2, (vs i).decode)/(1+∑ i, (ws i).decode),a.2)) := by
  have hvl : ∀ v ∈ List.ofFn vs, v.Valid := by intro v hm; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm; exact hv i
  have hwl : ∀ w ∈ List.ofFn ws, w.Valid := by intro w hm; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm; exact hw i
  have ht := tiltAtoms_decode (List.ofFn vs) (normalizer (List.ofFn ws)).1 (liftAtoms D as).1 hvl
  have hmask : interpretPolicy (n := n) (tiltAtoms (List.ofFn vs) (normalizer (List.ofFn ws)).1 (liftAtoms D as).1).1 =
      (((tiltAtoms (List.ofFn vs) (normalizer (List.ofFn ws)).1 (liftAtoms D as).1).1.map
        fun a => (a.1.decode,a.2)).map fun a => (a.1,maskSet (n := n) a.2)) := by simp [interpretPolicy,List.map_map]
  change interpretPolicy (n := n) (tiltAtoms _ _ _).1 = _
  rw [hmask,ht,liftAtoms_map]
  simp only [List.map_map,Function.comp_def,Decomposition.interpretGrid,interpretBitAtoms,
    normalizer_decode (List.ofFn ws) hwl]
  apply List.map_congr_left
  intro a ha
  rw [mask_sum_finite]
  simp [List.map_ofFn,List.sum_ofFn,Fraction.decode]


def policyBudget (n b m : ℕ) : ℕ := normalizerBudget n b + (4*m+1) +
  (m*(reverseBudget n b (displayWidth n b)+4)+1) + 8

theorem policyOutput_length (vs ws : List Fraction) (D : Bits) (as : List BitAtom) :
    (policyOutput vs ws D as).1.length = as.length := by
  simp [policyOutput,tiltAtoms_length,liftAtoms_map]

theorem policyOutput_cost (vs ws : List Fraction) (D : Bits) (as : List BitAtom)
    {n b : ℕ} (hvl : vs.length ≤ n) (hwl : ws.length ≤ n)
    (hv : ∀ v ∈ vs, v.Width b) (hw : ∀ w ∈ ws, w.Width b)
    (hD : D.length ≤ b) (hm : ∀ a ∈ as, a.1.length ≤ b) :
    (policyOutput vs ws D as).2 ≤ policyBudget n b as.length := by
  have hn := normalizer_width ws hwl hw
  have cn := normalizer_cost ws hwl hw
  have hmass : ∀ a ∈ (liftAtoms D as).1, a.1.Width b := by
    intro a ha
    rw [liftAtoms_map] at ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact ⟨hm x hx,hD⟩
  have ct := tiltAtoms_cost vs (normalizer ws).1 (liftAtoms D as).1 hvl hv hmass hn
  simp only [liftAtoms_map,List.length_map] at ct
  dsimp only [policyOutput,policyBudget]
  rw [liftAtoms_cost,liftAtoms_map]
  omega

/-- Output-size bound for all rational policy probabilities before any optional
canonical serialization. Masks are reused from sparse decomposition. -/
theorem tiltAtoms_width (vs : List Fraction) (normalizer : Fraction) (as : List PolicyAtom)
    {n b c : ℕ} (hvl : vs.length ≤ n) (hv : ∀ v ∈ vs, v.Width b)
    (hm : ∀ a ∈ as, a.1.Width b) (hn : normalizer.Width c) :
    ∀ a ∈ (tiltAtoms vs normalizer as).1, a.1.Width (reverseWidth n b c) := by
  induction as with
  | nil => simp [tiltAtoms]
  | cons a as ih =>
    intro x hx
    simp only [tiltAtoms,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact reverseWeight_width vs a.2 hvl hv (hm a (by simp)) hn
    · exact ih (fun a ha => hm a (by simp [ha])) x hx

theorem policyOutput_width (vs ws : List Fraction) (D : Bits) (as : List BitAtom)
    {n b : ℕ} (hvl : vs.length ≤ n) (hwl : ws.length ≤ n)
    (hv : ∀ v ∈ vs, v.Width b) (hw : ∀ w ∈ ws, w.Width b)
    (hD : D.length ≤ b) (hm : ∀ a ∈ as, a.1.length ≤ b) :
    ∀ a ∈ (policyOutput vs ws D as).1, a.1.Width (reverseWidth n b (displayWidth n b)) := by
  apply tiltAtoms_width vs (normalizer ws).1 (liftAtoms D as).1 hvl hv _ (normalizer_width ws hwl hw)
  intro a ha
  rw [liftAtoms_map] at ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  exact ⟨hm x hx,hD⟩

/-- Generic exact output validity, independent of any approximation assumption. -/
theorem policyOutput_valid {n K : ℕ} (vs ws : Fin n → Fraction) (D : Bits) (as : List BitAtom)
    (hv : ∀ i, (vs i).Valid) (hw : ∀ i, (ws i).Valid)
    (hvp : ∀ i, 0 < (vs i).decode)
    (hc : Decomposition.ValidDecomposition K (fun i => (ws i).decode/(vs i).decode)
      (Decomposition.interpretGrid (value D) (interpretBitAtoms (n := n) as))) :
    FPTAS.PolicyValid K (interpretPolicy (n := n)
      (policyOutput (List.ofFn vs) (List.ofFn ws) D as).1) ∧
    FPTAS.policySales (fun i => (vs i).decode) (interpretPolicy (n := n)
      (policyOutput (List.ofFn vs) (List.ofFn ws) D as).1) =
      Sales.compactSales (fun i => ((ws i).decode : ℝ)) := by
  rw [policyOutput_decode vs ws D as hv hw]
  exact FPTAS.reverse_list_correct (fun i => (vs i).decode) (fun i => (ws i).decode) hvp hc
end BalancedAssortments.FPTASCostPolicy
