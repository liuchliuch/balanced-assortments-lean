import BalancedAssortments.ComplexityTimeFixedSourceLanguage
import BalancedAssortments.SalesIntegration

/-! Exact original randomized-assortment interpretation of the binary decision
languages, including the fixed cardinality/perfect-balance restriction. -/
noncomputable section
namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeFractions ComplexityTimeSourcePipeline

/-- A finite randomized policy in the original MNL sales model. Every indexed
assortment satisfies the cardinality constraint, including unused atoms. -/
def SourcePolicyYes (s : Source) : Prop :=
  ∃ m,∃ (S : Fin m → Finset (Fin s.products.length)) (q : Fin m → ℝ),
    Sales.Distribution q ∧ (∀ a,(S a).card≤value s.capacity) ∧
    Sales.Balanced (decode s.alpha : ℝ)
      (Sales.sales (fun j => (decodedValues s.attractions j : ℝ)) S q) ∧
    (decode s.target : ℝ)≤Sales.revenue (fun j => (decodedValues s.prices j : ℝ))
      (Sales.sales (fun j => (decodedValues s.attractions j : ℝ)) S q)

theorem sourceYes_iff_policy (s : Source) (hs : LegalSource s) : SourceYes s ↔ SourcePolicyYes s := by
  have hv : ∀ j : Fin s.products.length,0<(decodedValues s.attractions j : ℝ) := by
    intro j
    exact_mod_cast (legal_verifier_conditions s hs).1 j |>.2
  constructor
  · rintro ⟨w,hw,hb,hr⟩
    obtain ⟨m,hm,S,q,hq,hK,he⟩ := Sales.compact_sparse_policy
      (fun j => (decodedValues s.attractions j : ℝ)) w hv hw
    refine ⟨m,S,q,hq,hK,?_,?_⟩
    · rw [he]
      exact (Sales.compact_balance _ w (fun j => (hw.1 j).1)).mpr hb
    · rwa [he,Sales.compact_revenue]
  · rintro ⟨m,S,q,hq,hK,hb,hr⟩
    obtain ⟨w,hw,he⟩ := Sales.policy_to_compact
      (fun j => (decodedValues s.attractions j : ℝ)) hv S hq (value s.capacity) hK
    refine ⟨w,hw,?_,?_⟩
    · rw [he] at hb
      exact (Sales.compact_balance _ w (fun j => (hw.1 j).1)).mp hb
    · rwa [he,Sales.compact_revenue] at hr

def PolicyLanguage (bits : List Bool) : Prop :=
  ∃ s,(parseSource bits).1=some s ∧ LegalSource s ∧ SourcePolicyYes s

def FixedPolicyLanguage (bits : List Bool) : Prop :=
  ∃ s,(parseSource bits).1=some s ∧ LegalSource s ∧ SourcePolicyYes s ∧
    value s.capacity=2 ∧ decode s.alpha=1

theorem policyLanguage_iff_source (bits : List Bool) : PolicyLanguage bits ↔ SourceLanguage bits := by
  constructor
  · rintro ⟨s,hp,hl,hy⟩;exact ⟨s,hp,hl,(sourceYes_iff_policy s hl).mpr hy⟩
  · rintro ⟨s,hp,hl,hy⟩;exact ⟨s,hp,hl,(sourceYes_iff_policy s hl).mp hy⟩

theorem fixedPolicyLanguage_iff_source (bits : List Bool) : FixedPolicyLanguage bits ↔ FixedSourceLanguage bits := by
  rw [fixedSourceLanguage_iff]
  constructor
  · rintro ⟨s,hp,hl,hy,hk,ha⟩;exact ⟨s,hp,hl,(sourceYes_iff_policy s hl).mpr hy,hk,ha⟩
  · rintro ⟨s,hp,hl,hy,hk,ha⟩;exact ⟨s,hp,hl,(sourceYes_iff_policy s hl).mp hy,hk,ha⟩
end BalancedAssortments.ComplexityTimeSourceParsing
