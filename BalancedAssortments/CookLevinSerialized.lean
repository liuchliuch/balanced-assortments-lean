import BalancedAssortments.CookLevinLabels
import BalancedAssortments.NPCNFThreeReduction

/-! Concrete self-delimiting CNF bitstream target. This module proves exact
semantic refinement; it does not assume polynomial time for Nat-based emission. -/
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

 def encodeLiteral (l : Literal) : Encoding.BitLiteral := ⟨l.var.bits,l.positive⟩
@[simp] lemma decode_encodeLiteral (l : Literal) : (encodeLiteral l).decode=l := by
  cases l
  simp [encodeLiteral,Encoding.BitLiteral.decode]

def encodeFormula (F : Formula) : Encoding.BitFormula := F.map (List.map encodeLiteral)
@[simp] lemma decode_encodeFormula (F : Formula) :
    (encodeFormula F).map (List.map Encoding.BitLiteral.decode)=F := by
  simp [encodeFormula,List.map_map,Function.comp_def]

def rawTableau (M : Machine) (word : List Bool) (T : ℕ) : Encoding.Raw :=
  let V := variableCount (M.stateExtra+1) (M.symbolExtra+3) (windowWidth word T) T (M.rules.length+1)
  ⟨(List.range V).map Nat.bits,encodeFormula (tableauFormula M word T)⟩

lemma rawTableau_decode (M : Machine) (word : List Bool) (T : ℕ) :
    (rawTableau M word T).decode=
      ⟨List.range (variableCount (M.stateExtra+1) (M.symbolExtra+3) (windowWidth word T) T (M.rules.length+1)),
        tableauFormula M word T⟩ := by
  simp [rawTableau,Encoding.Raw.decode,List.map_map,Function.comp_def]

lemma rawTableau_valid (M : Machine) (word : List Bool) (T : ℕ) :
    (rawTableau M word T).decode.Valid := by
  rw [rawTableau_decode]
  refine ⟨List.nodup_range,?_⟩
  intro c hc l hl
  exact List.mem_range.mpr (tableau_variables_bounded M word T c hc l hl)

def tableauBits (M : Machine) (word : List Bool) (T : ℕ) : List Bool :=
  Encoding.encode (rawTableau M word T)

/-- Exact many-one semantic map into the shared total CNF bitstream language.
The separate bit-generator and machine-time bounds are still required for a
polynomial-time reduction statement. -/
theorem tableauBits_correct (M : Machine) (word : List Bool) (T : ℕ) :
    Encoding.CNFLanguage (tableauBits M word T) ↔ AcceptsWithin M word T := by
  rw [tableauBits,Encoding.CNFLanguage_encode]
  rw [and_iff_right (rawTableau_valid M word T)]
  simp only [rawTableau_decode,Catalogued.Sat]
  exact tableau_satisfiable_iff_acceptsWithin M word T

theorem np_language_cnf_semantics (L : Set (List Bool)) (hL : InNP L) :
    ∃ M : Machine, ∃ p : Polynomial ℕ, ∀ word,
      Encoding.CNFLanguage (tableauBits M word (p.eval word.length)) ↔ word∈L := by
  obtain ⟨M,p,h⟩ := hL
  exact ⟨M,p,fun word => (tableauBits_correct M word _).trans (h word).symm⟩

end BalancedAssortments.CookLevin
