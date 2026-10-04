import BalancedAssortments.NPStackSourceVerifierGrammar

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

def productFields (p : ComplexityTimeFractions.Fraction×ComplexityTimeFractions.Fraction) : List (List Bool) :=
  [p.1.num.1,p.1.num.2,p.1.den,p.2.num.1,p.2.num.2,p.2.den]

theorem parseProducts_fields (fs : List (List Bool)) (ps : List (ComplexityTimeFractions.Fraction×ComplexityTimeFractions.Fraction))
    (h : (parseProducts fs).1=some ps) : fs=ps.flatMap productFields := by
  fun_induction parseProducts fs generalizing ps with
  | case1 => simp only [parseProducts,Option.some.injEq] at h;subst ps;rfl
  | case2 rp rn rd vp vn vd rest r ih =>
    subst r
    cases ht : (parseProducts rest).1 with
    | none => simp [ht] at h
    | some tail =>
      simp only [ht,Option.map_some,Option.some.injEq] at h
      subst ps
      simp only [List.flatMap_cons,productFields]
      rw [ih tail ht]
      rfl
  | case3 => simp_all [parseProducts]

def sourceFields (s : Source) : List (List Bool) :=
  [s.declaredCount,s.capacity,s.alpha.num.1,s.alpha.num.2,s.alpha.den,s.target.num.1,s.target.num.2,s.target.den]++
    s.products.flatMap productFields

theorem packSource_fields (fs : List (List Bool)) (s : Source)
    (h : (packSource fs).1=some s) : fs=sourceFields s := by
  fun_cases packSource fs with
  | case1 count K ap an ad hp hn hd rest =>
    cases ht : (parseProducts rest).1 with
    | none => simp [packSource,ht] at h
    | some ps =>
      simp [packSource,ht] at h
      subst s
      simp only [sourceFields]
      rw [parseProducts_fields rest ps ht]
      rfl
  | case2 => simp_all [packSource]

theorem parseTriples_fields (fs : List (List Bool)) (ms : List Bool) (ps : List ZBits)
    (h : (parseTriples fs).1=some (ms,ps)) :
    ∃ xs : List (Fin 3→List Bool),fs=xs.flatMap List.ofFn ∧
      xs.map (fun x=>(NPStackMask.maskValue (x 0)).getD false)=ms ∧
      xs.map (fun x=>(x 1,x 2))=ps ∧
      ∀ x∈xs,NPStackMask.maskValue (x 0)=some ((NPStackMask.maskValue (x 0)).getD false) := by
  fun_induction parseTriples fs generalizing ms ps with
  | case1 =>
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨[],rfl,rfl,rfl,by simp⟩
  | case2 mb pp pn rest m r ih =>
    subst m;subst r
    cases hm : (parseMask mb).1 with
    | none => simp [hm] at h
    | some b =>
      cases ht : (parseTriples rest).1 with
      | none => simp [hm,ht] at h
      | some tail =>
        rcases tail with ⟨ts,qs⟩
        simp only [hm,ht,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨xs,hfs,hms,hps,hgood⟩ := ih ts qs ht
        have hmask : NPStackMask.maskValue mb=some b := (NPStackMask.maskValue_parseMask mb).trans hm
        refine ⟨![mb,pp,pn]::xs,?_,?_,?_,?_⟩
        · simp [List.ofFn_succ,hfs]
        · simp [hmask,hms]
        · simp [hps]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · simp [hmask]
          · exact hgood x hx
  | case3 => simp_all

def productVector (p : ComplexityTimeFractions.Fraction×ComplexityTimeFractions.Fraction) : Fin 6→List Bool :=
  ![p.1.num.1,p.1.num.2,p.1.den,p.2.num.1,p.2.num.2,p.2.den]
def sourceHeaderFields (s : Source) : Fin 8→List Bool :=
  ![s.declaredCount,s.capacity,s.alpha.num.1,s.alpha.num.2,s.alpha.den,s.target.num.1,s.target.num.2,s.target.den]

lemma productVector_fields (p : ComplexityTimeFractions.Fraction×ComplexityTimeFractions.Fraction) :
    List.ofFn (productVector p)=productFields p := by simp [productVector,productFields,List.ofFn_succ]

lemma packSource_chunks (fs : List (List Bool)) (s : Source) (h : (packSource fs).1=some s) :
    ∃ hs : Fin 8→List Bool,∃ xs : List (Fin 6→List Bool),
      fs=List.ofFn hs++xs.flatMap List.ofFn ∧ xs.length=s.products.length := by
  refine ⟨sourceHeaderFields s,s.products.map productVector,?_,by simp⟩
  rw [packSource_fields fs s h]
  simp [sourceFields,sourceHeaderFields,List.ofFn_succ,List.flatMap_map,productVector,productFields]
  rfl

lemma packCertificate_chunks (fs : List (List Bool)) (c : Certificate) (h : (packCertificate fs).1=some c) :
    ∃ hc : Fin 2→List Bool,∃ xs : List (Fin 3→List Bool),
      fs=List.ofFn hc++xs.flatMap List.ofFn ∧ xs.length=c.numerators.length ∧
      ∀ x∈xs,NPStackMask.maskValue (x 0)=some ((NPStackMask.maskValue (x 0)).getD false) := by
  fun_cases packCertificate fs with
  | case1 qp qn rest =>
    cases ht : (parseTriples rest).1 with
    | none => simp [packCertificate,ht] at h
    | some pair =>
      rcases pair with ⟨ms,ps⟩
      simp [packCertificate,ht] at h
      subst c
      obtain ⟨xs,hfs,hms,hps,hgood⟩ := parseTriples_fields rest ms ps ht
      refine ⟨![qp,qn],xs,?_,?_,hgood⟩
      · simp [List.ofFn_succ,hfs]
      · have hh:=congrArg List.length hps
        simpa using hh
  | case2 => simp_all [packCertificate]

end BalancedAssortments.NPStack.SourceVerifier
