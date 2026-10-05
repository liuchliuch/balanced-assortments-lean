import BalancedAssortments

/-! Fixed interfaces for the official Comparator. -/
noncomputable section
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace BalancedAssortmentsAudit

/-- T1: `BalancedAssortments.Sales.exact_attainable`. -/
theorem claim_001 :
  (∀ {n K : ℕ} (v x : Fin n → ℝ) (hv : ∀ i, 0 < v i),
  (∃ m, ∃ (S : Fin m → Finset (Fin n)) (q : Fin m → ℝ),
    BalancedAssortments.Sales.Distribution q ∧ (∀ a, (S a).card ≤ K) ∧
    BalancedAssortments.Sales.sales v S q = x) ↔
  ∃ w, BalancedAssortments.Sales.CompactFeasible v w K ∧
    BalancedAssortments.Sales.compactSales w = x) := by
  sorry

/-- T1: `BalancedAssortments.Sales.compact_sparse_policy`. -/
theorem claim_002 :
  (∀ {n K : Nat} (v w : Fin n → Real)
  (hv :
    ∀ (i : Fin n),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  (hw : @BalancedAssortments.Sales.CompactFeasible.{0} (Fin n) (Fin.fintype n) v w K),
  @Exists.{1} Nat fun (m : Nat) =>
    And
      (@LE.le.{0} Nat instLENat m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Exists.{1} (Fin m → Finset.{0} (Fin n)) fun (S : Fin m → Finset.{0} (Fin n)) =>
        @Exists.{1} (Fin m → Real) fun (q : Fin m → Real) =>
          And (@BalancedAssortments.Sales.Distribution.{0} (Fin m) (Fin.fintype m) q)
            (And (∀ (a : Fin m), @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) (S a)) K)
              (@Eq.{1} ((i : Fin n) → Real)
                (@BalancedAssortments.Sales.sales.{0, 0} (Fin n) (Fin m) (instDecidableEqFin n) (Fin.fintype m) v S q)
                (@BalancedAssortments.Sales.compactSales.{0} (Fin n) (Fin.fintype n) w))))) := by
  sorry

/-- T1: `BalancedAssortments.Sales.optimization_sparse_policy`. -/
theorem claim_003 :
  (∀ {n K : Nat} (v r w : Fin n → Real) (α : Real)
  (hv :
    ∀ (i : Fin n),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  (hw :
    @BalancedAssortments.Optimization.feasible.{0} (Fin n) (Fin.fintype n) v α (@Nat.cast.{0} Real Real.instNatCast K)
      w),
  @Exists.{1} Nat fun (m : Nat) =>
    And
      (@LE.le.{0} Nat instLENat m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Exists.{1} (Fin m → Finset.{0} (Fin n)) fun (S : Fin m → Finset.{0} (Fin n)) =>
        @Exists.{1} (Fin m → Real) fun (q : Fin m → Real) =>
          And (@BalancedAssortments.Sales.Distribution.{0} (Fin m) (Fin.fintype m) q)
            (And (∀ (a : Fin m), @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) (S a)) K)
              (And
                (@BalancedAssortments.Sales.Balanced.{0} (Fin n) α
                  (@BalancedAssortments.Sales.sales.{0, 0} (Fin n) (Fin m) (instDecidableEqFin n) (Fin.fintype m) v S
                    q))
                (@Eq.{1} Real
                  (@BalancedAssortments.Sales.revenue.{0} (Fin n) (Fin.fintype n) r
                    (@BalancedAssortments.Sales.sales.{0, 0} (Fin n) (Fin m) (instDecidableEqFin n) (Fin.fintype m) v S
                      q))
                  (@BalancedAssortments.Optimization.revenue.{0} (Fin n) (Fin.fintype n) r w)))))) := by
  sorry

/-- T1: `BalancedAssortments.Sales.rational_sparse_policy`. -/
theorem claim_004 :
  (∀ {n K : Nat} (v w : Fin n → Rat)
  (hv : ∀ (i : Fin n), @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (v i))
  (hc :
    ∀ (i : Fin n),
      And (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (w i))
        (@LE.le.{0} Rat Rat.instLE (w i) (v i)))
  (hr :
    @LE.le.{0} Rat Rat.instLE
      (@Finset.sum.{0, 0} (Fin n) Rat Rat.addCommMonoid (@Finset.univ.{0} (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) (w i) (v i))
      (@Nat.cast.{0} Rat Rat.instNatCast K)),
  @Exists.{1} (List.{0} (BalancedAssortments.Decomposition.Atom n))
    fun (p : List.{0} (BalancedAssortments.Decomposition.Atom n)) =>
    @Exists.{1} (Fin (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p) → Rat)
      fun (q : Fin (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p) → Rat) =>
      And
        (@LE.le.{0} Nat instLENat (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (@BalancedAssortments.Sales.Distribution.{0}
            (Fin (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p))
            (Fin.fintype (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p))
            fun (a : Fin (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p)) =>
            @Rat.cast.{0} Real Real.instRatCast (q a))
          (And
            (∀ (a : Fin (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p)),
              @Ne.{1} Rat (q a) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) →
                @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) (@BalancedAssortments.Sales.certificateSets n p a))
                  K)
            (@Eq.{1} ((i : Fin n) → Real)
              (@BalancedAssortments.Sales.sales.{0, 0} (Fin n)
                (Fin (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p)) (instDecidableEqFin n)
                (Fin.fintype (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p))
                (fun (i : Fin n) => @Rat.cast.{0} Real Real.instRatCast (v i))
                (@BalancedAssortments.Sales.certificateSets n p)
                fun (a : Fin (@List.length.{0} (BalancedAssortments.Decomposition.Atom n) p)) =>
                @Rat.cast.{0} Real Real.instRatCast (q a))
              (@BalancedAssortments.Sales.compactSales.{0} (Fin n) (Fin.fintype n) fun (i : Fin n) =>
                @Rat.cast.{0} Real Real.instRatCast (w i)))))) := by
  sorry

/-- T1: `BalancedAssortments.Decomposition.CostMachine.raw_binary_sparse_decomposition`. -/
theorem claim_005 :
  (∀ {n L : Nat} (ks : BalancedAssortments.Decomposition.CostMachine.Bits)
  (xs ys : List.{0} BalancedAssortments.Decomposition.CostMachine.Bits)
  (hx : @Eq.{1} Nat (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.Bits xs) n)
  (hy : @Eq.{1} Nat (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.Bits ys) n)
  (hd :
    ∀ (i : Fin n),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (BalancedAssortments.ComplexityTimeBinary.value
          (@Option.getD.{0} BalancedAssortments.Decomposition.CostMachine.Bits
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) Nat
              BalancedAssortments.Decomposition.CostMachine.Bits
              (fun (as : List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) (i : Nat) =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.Bits as))
              (@List.instGetElem?NatLtLength.{0} BalancedAssortments.Decomposition.CostMachine.Bits) ys (@Fin.val n i))
            (@List.nil.{0} Bool))))
  (h :
    @BalancedAssortments.Decomposition.Feasible n (BalancedAssortments.ComplexityTimeBinary.value ks) fun (i : Fin n) =>
      @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@Nat.cast.{0} Rat Rat.instNatCast
          (BalancedAssortments.ComplexityTimeBinary.value
            (@Option.getD.{0} BalancedAssortments.Decomposition.CostMachine.Bits
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) Nat
                BalancedAssortments.Decomposition.CostMachine.Bits
                (fun (as : List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) (i : Nat) =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.Bits as))
                (@List.instGetElem?NatLtLength.{0} BalancedAssortments.Decomposition.CostMachine.Bits) xs
                (@Fin.val n i))
              (@List.nil.{0} Bool))))
        (@Nat.cast.{0} Rat Rat.instNatCast
          (BalancedAssortments.ComplexityTimeBinary.value
            (@Option.getD.{0} BalancedAssortments.Decomposition.CostMachine.Bits
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) Nat
                BalancedAssortments.Decomposition.CostMachine.Bits
                (fun (as : List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) (i : Nat) =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.Bits as))
                (@List.instGetElem?NatLtLength.{0} BalancedAssortments.Decomposition.CostMachine.Bits) ys
                (@Fin.val n i))
              (@List.nil.{0} Bool)))))
  (hK : @LE.le.{0} Nat instLENat (BalancedAssortments.ComplexityTimeBinary.value ks) n)
  (hL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (BalancedAssortments.Decomposition.CostMachine.bitVolume xs)
        (BalancedAssortments.Decomposition.CostMachine.bitVolume ys))
      L),
  have out :
    Prod.{0, 0} BalancedAssortments.Decomposition.CostMachine.Bits
      (Prod.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat) :=
    BalancedAssortments.Decomposition.CostMachine.binaryGreedyRank ks xs ys;
  have z : (i : Fin n) → Rat := fun (i : Fin n) =>
    @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@Nat.cast.{0} Rat Rat.instNatCast
        (BalancedAssortments.ComplexityTimeBinary.value
          (@Option.getD.{0} BalancedAssortments.Decomposition.CostMachine.Bits
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) Nat
              BalancedAssortments.Decomposition.CostMachine.Bits
              (fun (as : List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) (i : Nat) =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.Bits as))
              (@List.instGetElem?NatLtLength.{0} BalancedAssortments.Decomposition.CostMachine.Bits) xs (@Fin.val n i))
            (@List.nil.{0} Bool))))
      (@Nat.cast.{0} Rat Rat.instNatCast
        (BalancedAssortments.ComplexityTimeBinary.value
          (@Option.getD.{0} BalancedAssortments.Decomposition.CostMachine.Bits
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) Nat
              BalancedAssortments.Decomposition.CostMachine.Bits
              (fun (as : List.{0} BalancedAssortments.Decomposition.CostMachine.Bits) (i : Nat) =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.Bits as))
              (@List.instGetElem?NatLtLength.{0} BalancedAssortments.Decomposition.CostMachine.Bits) ys (@Fin.val n i))
            (@List.nil.{0} Bool))));
  have p : List.{0} (BalancedAssortments.Decomposition.Atom n) :=
    @BalancedAssortments.Decomposition.interpretGrid n
      (BalancedAssortments.ComplexityTimeBinary.value
        (@Prod.fst.{0, 0} BalancedAssortments.Decomposition.CostMachine.Bits
          (Prod.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat) out))
      (@BalancedAssortments.Decomposition.CostMachine.interpretBitAtoms n
        (@Prod.fst.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat
          (@Prod.snd.{0, 0} BalancedAssortments.Decomposition.CostMachine.Bits
            (Prod.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat) out)));
  And (@BalancedAssortments.Decomposition.ValidDecomposition n (BalancedAssortments.ComplexityTimeBinary.value ks) z p)
    (And
      (∀ (a : BalancedAssortments.Decomposition.Atom n),
        @Membership.mem.{0, 0} (BalancedAssortments.Decomposition.Atom n)
            (List.{0} (BalancedAssortments.Decomposition.Atom n))
            (@List.instMembership.{0} (BalancedAssortments.Decomposition.Atom n)) p a →
          And
            (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (@Prod.fst.{0, 0} Rat (Finset.{0} (Fin n)) a))
            (@LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin n) (@Prod.snd.{0, 0} Rat (Finset.{0} (Fin n)) a))
              (BalancedAssortments.ComplexityTimeBinary.value ks)))
      (And
        (@LE.le.{0} Nat instLENat
          (@List.length.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom
            (@Prod.fst.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat
              (@Prod.snd.{0, 0} BalancedAssortments.Decomposition.CostMachine.Bits
                (Prod.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat) out)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@LE.le.{0} Nat instLENat
          (@Prod.snd.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat
            (@Prod.snd.{0, 0} BalancedAssortments.Decomposition.CostMachine.Bits
              (Prod.{0, 0} (List.{0} BalancedAssortments.Decomposition.CostMachine.BitAtom) Nat) out))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 8192) (instOfNatNat (nat_lit 8192)))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Bool ks)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) := by
  sorry

/-- T2: `BalancedAssortments.PaperTheoremTwo.fixed_policy_npComplete`. -/
theorem claim_006 :
  (BalancedAssortments.NPStack.NPComplete BalancedAssortments.ComplexityTimeSourceParsing.FixedPolicyLanguage) := by
  sorry

/-- T2: `BalancedAssortments.PaperTheoremTwo.policy_npComplete`. -/
theorem claim_007 :
  (BalancedAssortments.NPStack.NPComplete BalancedAssortments.ComplexityTimeSourceParsing.PolicyLanguage) := by
  sorry

/-- T2: `BalancedAssortments.PaperTheoremTwo.np_reduces_fixed_source`. -/
theorem claim_008 :
  (∀ (L : Set.{0} (List.{0} Bool)) (hL : BalancedAssortments.NPMachine.InNP L),
  BalancedAssortments.NPStack.PolyManyOne L BalancedAssortments.ComplexityTimeSourceParsing.FixedSourceLanguage) := by
  sorry

/-- T2: `BalancedAssortments.PaperTheoremTwo.np_reduces_source`. -/
theorem claim_009 :
  (∀ (L : Set.{0} (List.{0} Bool)) (hL : BalancedAssortments.NPMachine.InNP L),
  BalancedAssortments.NPStack.PolyManyOne L BalancedAssortments.ComplexityTimeSourceParsing.SourceLanguage) := by
  sorry

/-- T3: `BalancedAssortments.FPTASCostCodec.flat_policy_fptas`. -/
theorem claim_010 :
  (∀ {n : Nat} (d : BalancedAssortments.FPTAS.Input n) (hd : @BalancedAssortments.FPTAS.Valid n d) (ε : Rat)
  (hε : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε)
  (hε1 : @LT.lt.{0} Rat Rat.instLT ε (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (alpha epsilon : BalancedAssortments.KnapsackCostRational.Fraction) (ks : List.{0} Bool)
  (rv :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      BalancedAssortments.FPTASCostSeeds.Product)
  (ha : BalancedAssortments.KnapsackCostRational.Fraction.Valid alpha)
  (he : BalancedAssortments.KnapsackCostRational.Fraction.Valid epsilon)
  (had :
    @Eq.{1} Rat (BalancedAssortments.KnapsackCostRational.Fraction.decode alpha)
      (@BalancedAssortments.FPTAS.Input.α n d))
  (hed : @Eq.{1} Rat (BalancedAssortments.KnapsackCostRational.Fraction.decode epsilon) ε)
  (hK : @Eq.{1} Nat (BalancedAssortments.ComplexityTimeBinary.value ks) (@BalancedAssortments.FPTAS.Input.K n d))
  (hprod :
    ∀
      (i :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      And
        (BalancedAssortments.KnapsackCostRational.Fraction.Valid
          (@Prod.fst.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
            BalancedAssortments.KnapsackCostRational.Fraction (rv i)))
        (BalancedAssortments.KnapsackCostRational.Fraction.Valid
          (@Prod.snd.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
            BalancedAssortments.KnapsackCostRational.Fraction (rv i))))
  (hdec :
    ∀
      (i :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      And
        (@Eq.{1} Rat
          (BalancedAssortments.KnapsackCostRational.Fraction.decode
            (@Prod.fst.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
              BalancedAssortments.KnapsackCostRational.Fraction (rv i)))
          (@BalancedAssortments.FPTAS.Input.r n d i))
        (@Eq.{1} Rat
          (BalancedAssortments.KnapsackCostRational.Fraction.decode
            (@Prod.snd.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
              BalancedAssortments.KnapsackCostRational.Fraction (rv i)))
          (@BalancedAssortments.FPTAS.Input.v n d i)))
  (bits : List.{0} Bool)
  (hparse :
    @Eq.{1} (Option.{0} BalancedAssortments.FPTASCostCodec.Input)
      (@Prod.fst.{0, 0} (Option.{0} BalancedAssortments.FPTASCostCodec.Input) Nat
        (BalancedAssortments.FPTASCostCodec.parse bits))
      (@Option.some.{0} BalancedAssortments.FPTASCostCodec.Input
        (BalancedAssortments.FPTASCostCodec.Input.mk alpha epsilon ks
          (@BalancedAssortments.FPTASCostProgram.sourceProducts n rv)))),
  @Exists.{1} (List.{0} Bool) fun (output : List.{0} Bool) =>
    @Exists.{1} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom)
      fun (atoms : List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) =>
      And
        (@Eq.{1} (Option.{0} (List.{0} Bool))
          (@Prod.fst.{0, 0} (Option.{0} (List.{0} Bool)) Nat (BalancedAssortments.FPTASCostCodec.run bits))
          (@Option.some.{0} (List.{0} Bool) output))
        (And
          (@Eq.{1} (Option.{0} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom))
            (BalancedAssortments.FPTASCostCodec.decodeOutput output)
            (@Option.some.{0} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) atoms))
          (And
            (@BalancedAssortments.FPTAS.PolicyValid
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@BalancedAssortments.FPTAS.Input.K n d)
              (@BalancedAssortments.FPTASCostPolicy.interpretPolicy
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                atoms))
            (And
              (@BalancedAssortments.Sales.Balanced.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.α n d))
                (@BalancedAssortments.FPTAS.policySales
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@BalancedAssortments.FPTAS.Input.v n d)
                  (@BalancedAssortments.FPTASCostPolicy.interpretPolicy
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    atoms)))
              (And
                (@LE.le.{0} Nat instLENat (@List.length.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom atoms)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (And
                  (∀ (a : BalancedAssortments.FPTASCostOutput.PolicyAtom),
                    @Membership.mem.{0, 0} BalancedAssortments.FPTASCostOutput.PolicyAtom
                        (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom)
                        (@List.instMembership.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) atoms a →
                      And
                        (BalancedAssortments.KnapsackCostRational.Fraction.Valid
                          (@Prod.fst.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction (List.{0} Bool) a))
                        (@Eq.{1} Nat
                          (@List.length.{0} Bool
                            (@Prod.snd.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction (List.{0} Bool) a))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (∀
                      (u :
                        Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Real),
                      @BalancedAssortments.Optimization.feasible.{0}
                          (Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin.fintype
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (fun
                              (i :
                                Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                            @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.v n d i))
                          (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.α n d))
                          (@Nat.cast.{0} Real Real.instNatCast (@BalancedAssortments.FPTAS.Input.K n d)) u →
                        @LE.le.{0} Real Real.instLE
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@Rat.cast.{0} Real Real.instRatCast ε))
                            (@BalancedAssortments.Optimization.revenue.{0}
                              (Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (Fin.fintype
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (fun
                                  (i :
                                    Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
                              u))
                          (@BalancedAssortments.Sales.revenue.{0}
                            (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (Fin.fintype
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (fun
                                (i :
                                  Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                              @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
                            (@BalancedAssortments.FPTAS.policySales
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@BalancedAssortments.FPTAS.Input.v n d)
                              (@BalancedAssortments.FPTASCostPolicy.interpretPolicy
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                atoms))))
                    (@LE.le.{0} Nat instLENat
                      (@Prod.snd.{0, 0} (Option.{0} (List.{0} Bool)) Nat (BalancedAssortments.FPTASCostCodec.run bits))
                      (@DFunLike.coe.{1, 1, 1}
                        (@RingHom.{0, 0}
                          (@MvPolynomial.{0, 0}
                            (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                            Nat Nat.instCommSemiring)
                          Nat
                          (@Semiring.toNonAssocSemiring.{0}
                            (@MvPolynomial.{0, 0}
                              (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                              Nat Nat.instCommSemiring)
                            (@CommSemiring.toSemiring.{0}
                              (@MvPolynomial.{0, 0}
                                (Fin
                                  (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                Nat Nat.instCommSemiring)
                              (@MvPolynomial.commSemiring.{0, 0} Nat
                                (Fin
                                  (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                Nat.instCommSemiring)))
                          (@Semiring.toNonAssocSemiring.{0} Nat
                            (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring)))
                        (@MvPolynomial.{0, 0}
                          (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) Nat
                          Nat.instCommSemiring)
                        (fun
                            (x :
                              @MvPolynomial.{0, 0}
                                (Fin
                                  (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                Nat Nat.instCommSemiring) =>
                          Nat)
                        (@RingHom.instFunLike.{0, 0}
                          (@MvPolynomial.{0, 0}
                            (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                            Nat Nat.instCommSemiring)
                          Nat
                          (@Semiring.toNonAssocSemiring.{0}
                            (@MvPolynomial.{0, 0}
                              (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                              Nat Nat.instCommSemiring)
                            (@CommSemiring.toSemiring.{0}
                              (@MvPolynomial.{0, 0}
                                (Fin
                                  (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                Nat Nat.instCommSemiring)
                              (@MvPolynomial.commSemiring.{0, 0} Nat
                                (Fin
                                  (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                Nat.instCommSemiring)))
                          (@Semiring.toNonAssocSemiring.{0} Nat
                            (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring)))
                        (@MvPolynomial.eval.{0, 0} Nat
                          (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                          Nat.instCommSemiring
                          (@Matrix.vecCons.{0} Nat
                            (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@List.length.{0} Bool bits)
                            (@Matrix.vecCons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (@Nat.ceil.{0} Rat Rat.semiring Rat.instPartialOrder
                                (@FloorRing.toFloorSemiring.{0} Rat
                                  (@NormedRing.toRing.{0} Rat
                                    (@NormedCommRing.toNormedRing.{0} Rat
                                      (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField)))
                                  Rat.linearOrder Rat.instIsStrictOrderedRing Rat.instFloorRing)
                                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                  (@OfNat.ofNat.{0} Rat (nat_lit 10) (@Rat.instOfNat (nat_lit 10))) ε))
                              (@Matrix.vecEmpty.{0} Nat))))
                        BalancedAssortments.FPTASCostCodec.flatPolynomial))))))))) := by
  sorry

/-- T3: `BalancedAssortments.FPTASCostComplete.binary_policy_fptas`. -/
theorem claim_011 :
  (∀ {n : Nat} (d : BalancedAssortments.FPTAS.Input n) (hd : @BalancedAssortments.FPTAS.Valid n d) (ε : Rat)
  (hε : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε)
  (hε1 : @LT.lt.{0} Rat Rat.instLT ε (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (alpha epsilon : BalancedAssortments.KnapsackCostRational.Fraction) (ks : List.{0} Bool)
  (rv :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      BalancedAssortments.FPTASCostSeeds.Product)
  (ha : BalancedAssortments.KnapsackCostRational.Fraction.Valid alpha)
  (he : BalancedAssortments.KnapsackCostRational.Fraction.Valid epsilon)
  (had :
    @Eq.{1} Rat (BalancedAssortments.KnapsackCostRational.Fraction.decode alpha)
      (@BalancedAssortments.FPTAS.Input.α n d))
  (hed : @Eq.{1} Rat (BalancedAssortments.KnapsackCostRational.Fraction.decode epsilon) ε)
  (hK : @Eq.{1} Nat (BalancedAssortments.ComplexityTimeBinary.value ks) (@BalancedAssortments.FPTAS.Input.K n d))
  (hprod :
    ∀
      (i :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      And
        (BalancedAssortments.KnapsackCostRational.Fraction.Valid
          (@Prod.fst.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
            BalancedAssortments.KnapsackCostRational.Fraction (rv i)))
        (BalancedAssortments.KnapsackCostRational.Fraction.Valid
          (@Prod.snd.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
            BalancedAssortments.KnapsackCostRational.Fraction (rv i))))
  (hdec :
    ∀
      (i :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      And
        (@Eq.{1} Rat
          (BalancedAssortments.KnapsackCostRational.Fraction.decode
            (@Prod.fst.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
              BalancedAssortments.KnapsackCostRational.Fraction (rv i)))
          (@BalancedAssortments.FPTAS.Input.r n d i))
        (@Eq.{1} Rat
          (BalancedAssortments.KnapsackCostRational.Fraction.decode
            (@Prod.snd.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction
              BalancedAssortments.KnapsackCostRational.Fraction (rv i)))
          (@BalancedAssortments.FPTAS.Input.v n d i))),
  have out : Prod.{0, 0} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) Nat :=
    BalancedAssortments.FPTASCostComplete.runPolicyBits alpha epsilon ks
      (@BalancedAssortments.FPTASCostProgram.sourceProducts n rv);
  have policy :
    List.{0}
      (BalancedAssortments.Decomposition.Atom
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) :=
    @BalancedAssortments.FPTASCostPolicy.interpretPolicy
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Prod.fst.{0, 0} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) Nat out);
  have I : Nat :=
    @List.length.{0} Bool
      (BalancedAssortments.FPTASCostProgram.serializeInput alpha epsilon
        (BalancedAssortments.KnapsackCostRational.Fraction.mk ks (@List.cons.{0} Bool Bool.true (@List.nil.{0} Bool)))
        (@BalancedAssortments.FPTASCostProgram.sourceProducts n rv));
  And
    (@BalancedAssortments.FPTAS.PolicyValid
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@BalancedAssortments.FPTAS.Input.K n d) policy)
    (And
      (@BalancedAssortments.Sales.Balanced.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.α n d))
        (@BalancedAssortments.FPTAS.policySales
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@BalancedAssortments.FPTAS.Input.v n d) policy))
      (And
        (@LE.le.{0} Nat instLENat
          (@List.length.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom
            (@Prod.fst.{0, 0} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) Nat out))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (And
          (∀ (a : BalancedAssortments.FPTASCostOutput.PolicyAtom),
            @Membership.mem.{0, 0} BalancedAssortments.FPTASCostOutput.PolicyAtom
                (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom)
                (@List.instMembership.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom)
                (@Prod.fst.{0, 0} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) Nat out) a →
              And
                (BalancedAssortments.KnapsackCostRational.Fraction.Valid
                  (@Prod.fst.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction (List.{0} Bool) a))
                (@Eq.{1} Nat
                  (@List.length.{0} Bool
                    (@Prod.snd.{0, 0} BalancedAssortments.KnapsackCostRational.Fraction (List.{0} Bool) a))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (And
            (∀
              (u :
                Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  Real),
              @BalancedAssortments.Optimization.feasible.{0}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (fun
                      (i :
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                    @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.v n d i))
                  (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.α n d))
                  (@Nat.cast.{0} Real Real.instNatCast (@BalancedAssortments.FPTAS.Input.K n d)) u →
                @LE.le.{0} Real Real.instLE
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Rat.cast.{0} Real Real.instRatCast ε))
                    (@BalancedAssortments.Optimization.revenue.{0}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (fun
                          (i :
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
                      u))
                  (@BalancedAssortments.Sales.revenue.{0}
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin.fintype
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (fun
                        (i :
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
                    (@BalancedAssortments.FPTAS.policySales
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@BalancedAssortments.FPTAS.Input.v n d) policy)))
            (@LE.le.{0} Nat instLENat
              (@Prod.snd.{0, 0} (List.{0} BalancedAssortments.FPTASCostOutput.PolicyAtom) Nat out)
              (@DFunLike.coe.{1, 1, 1}
                (@RingHom.{0, 0}
                  (@MvPolynomial.{0, 0}
                    (Fin (Nat.succ (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Nat Nat.instCommSemiring)
                  Nat
                  (@Semiring.toNonAssocSemiring.{0}
                    (@MvPolynomial.{0, 0}
                      (Fin
                        (Nat.succ (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      Nat Nat.instCommSemiring)
                    (@CommSemiring.toSemiring.{0}
                      (@MvPolynomial.{0, 0}
                        (Fin
                          (Nat.succ
                            (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        Nat Nat.instCommSemiring)
                      (@MvPolynomial.commSemiring.{0, 0} Nat
                        (Fin
                          (Nat.succ
                            (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        Nat.instCommSemiring)))
                  (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring)))
                (@MvPolynomial.{0, 0}
                  (Fin (Nat.succ (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Nat Nat.instCommSemiring)
                (fun
                    (x :
                      @MvPolynomial.{0, 0}
                        (Fin
                          (Nat.succ
                            (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        Nat Nat.instCommSemiring) =>
                  Nat)
                (@RingHom.instFunLike.{0, 0}
                  (@MvPolynomial.{0, 0}
                    (Fin (Nat.succ (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Nat Nat.instCommSemiring)
                  Nat
                  (@Semiring.toNonAssocSemiring.{0}
                    (@MvPolynomial.{0, 0}
                      (Fin
                        (Nat.succ (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      Nat Nat.instCommSemiring)
                    (@CommSemiring.toSemiring.{0}
                      (@MvPolynomial.{0, 0}
                        (Fin
                          (Nat.succ
                            (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        Nat Nat.instCommSemiring)
                      (@MvPolynomial.commSemiring.{0, 0} Nat
                        (Fin
                          (Nat.succ
                            (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        Nat.instCommSemiring)))
                  (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring)))
                (@MvPolynomial.eval.{0, 0} Nat
                  (Fin (Nat.succ (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Nat.instCommSemiring
                  (@Matrix.vecCons.{0} Nat
                    (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) I
                    (@Matrix.vecCons.{0} Nat (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) I
                      (@Matrix.vecCons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Nat.ceil.{0} Rat Rat.semiring Rat.instPartialOrder
                          (@FloorRing.toFloorSemiring.{0} Rat
                            (@NormedRing.toRing.{0} Rat
                              (@NormedCommRing.toNormedRing.{0} Rat
                                (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField)))
                            Rat.linearOrder Rat.instIsStrictOrderedRing Rat.instFloorRing)
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (@OfNat.ofNat.{0} Rat (nat_lit 10) (@Rat.instOfNat (nat_lit 10))) ε))
                        (@Matrix.vecEmpty.{0} Nat)))))
                BalancedAssortments.FPTASCostComplete.policyPolynomial))))))) := by
  sorry

/-- T3: `BalancedAssortments.FPTAS.runPolicy_approximation`. -/
theorem claim_012.{u_1} :
  (∀ {n : Nat} (d : BalancedAssortments.FPTAS.Input n) (hd : @BalancedAssortments.FPTAS.Valid n d) (ε : Rat)
  (hε : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε)
  (hε1 : @LT.lt.{0} Rat Rat.instLT ε (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) {A : Type u_1}
  [inst : Fintype.{u_1} A]
  (S :
    A →
      Finset.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (q : A → Real) (hq : @BalancedAssortments.Sales.Distribution.{u_1} A inst q)
  (hK :
    ∀ (a : A),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (S a))
        (@BalancedAssortments.FPTAS.Input.K n d))
  (hb :
    @BalancedAssortments.Sales.Balanced.{0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.α n d))
      (@BalancedAssortments.Sales.sales.{0, u_1}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        A
        (instDecidableEqFin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        inst
        (fun
            (i :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.v n d i))
        S q)),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@Rat.cast.{0} Real Real.instRatCast ε))
      (@BalancedAssortments.Sales.revenue.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (fun
            (i :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
        (@BalancedAssortments.Sales.sales.{0, u_1}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          A
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          inst
          (fun
              (i :
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
            @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.v n d i))
          S q)))
    (@BalancedAssortments.Sales.revenue.{0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (Fin.fintype
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (fun
          (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
        @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
      (@BalancedAssortments.FPTAS.policySales
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@BalancedAssortments.FPTAS.Input.v n d) (@BalancedAssortments.FPTAS.runPolicy n d ε)))) := by
  sorry

/-- P4: `BalancedAssortments.FixedSupportAmbient.ambient_prescribed_support_serialized`. -/
theorem claim_013 :
  (@Exists.{1} (@Polynomial.{0} Nat Nat.instSemiring) fun (P : @Polynomial.{0} Nat Nat.instSemiring) =>
  ∀ {N : Nat} (A : Finset.{0} (Fin N)) (hA : @Finset.Nonempty.{0} (Fin N) A)
    (data : Fin N → BalancedAssortments.FixedSupportCostPoints.Product) (mask : Fin N → Bool) (r v : Fin N → Rat)
    (α K : BalancedAssortments.FixedSupportCostRational.Fraction),
    (∀ (i : Fin N),
        Iff (@Eq.{1} Bool (mask i) Bool.true)
          (@Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N)) (@Finset.instMembership.{0} (Fin N)) A i)) →
      (∀ (i : Fin N), BalancedAssortments.FixedSupportCostPoints.Product.Valid (data i)) →
        (∀ (i : Fin N),
            @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (r i)) →
          (∀ (i : Fin N),
              @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (v i)) →
            BalancedAssortments.ComplexityTimeFractions.Valid α →
              BalancedAssortments.ComplexityTimeFractions.Valid K →
                @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                    (BalancedAssortments.ComplexityTimeFractions.decode α) →
                  @LE.le.{0} Rat Rat.instLE (BalancedAssortments.ComplexityTimeFractions.decode α)
                      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) →
                    @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                        (BalancedAssortments.ComplexityTimeFractions.decode K) →
                      (∀ (i : Fin N),
                          And
                            (@Eq.{1} Rat
                              (BalancedAssortments.ComplexityTimeFractions.decode
                                (@Prod.fst.{0, 0} BalancedAssortments.FixedSupportCostRational.Fraction
                                  BalancedAssortments.FixedSupportCostRational.Fraction (data i)))
                              (r i))
                            (@Eq.{1} Rat
                              (BalancedAssortments.ComplexityTimeFractions.decode
                                (@Prod.snd.{0, 0} BalancedAssortments.FixedSupportCostRational.Fraction
                                  BalancedAssortments.FixedSupportCostRational.Fraction (data i)))
                              (v i))) →
                        And
                          (@Exists.{1} BalancedAssortments.FixedSupportAmbientPreprocess.Prepared
                            fun (prepared : BalancedAssortments.FixedSupportAmbientPreprocess.Prepared) =>
                            @Exists.{1}
                              (BalancedAssortments.FixedSupportCostMax.Result.{0}
                                (Fin
                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products prepared))))
                              fun
                                (out :
                                  BalancedAssortments.FixedSupportCostMax.Result.{0}
                                    (Fin
                                      (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                        (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                          prepared)))) =>
                              @Exists.{1}
                                (Equiv.{1, 1}
                                  (Fin
                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products prepared)))
                                  (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                    @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                      (@Finset.instMembership.{0} (Fin N)) A x))
                                fun
                                  (e :
                                    Equiv.{1, 1}
                                      (Fin
                                        (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                          (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                            prepared)))
                                      (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                        @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                          (@Finset.instMembership.{0} (Fin N)) A x)) =>
                                @Exists.{1} (Prod.{0, 0} Rat Rat) fun (p : Prod.{0, 0} Rat Rat) =>
                                  And
                                    (@Eq.{1}
                                      (Option.{0} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult)
                                      (@Prod.fst.{0, 0}
                                        (Option.{0} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult) Nat
                                        (BalancedAssortments.FixedSupportAmbientPreprocess.runAmbient α K
                                          (@List.ofFn.{0} BalancedAssortments.FixedSupportCostPoints.Product N data)
                                          (@List.ofFn.{0} Bool N mask)))
                                      (@Option.some.{0} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult
                                        (@Sigma.mk.{0, 0} BalancedAssortments.FixedSupportAmbientPreprocess.Prepared
                                          (fun (out : BalancedAssortments.FixedSupportAmbientPreprocess.Prepared) =>
                                            BalancedAssortments.FixedSupportCostMax.Result.{0}
                                              (Fin
                                                (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                    out))))
                                          prepared out)))
                                    (And
                                      (@BalancedAssortments.FixedSupportCostProgram.Realizes
                                        (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                          (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                            prepared))
                                        (fun
                                            (j :
                                              Fin
                                                (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                    prepared))) =>
                                          r
                                            (@Subtype.val.{1} (Fin N)
                                              (fun (x : Fin N) =>
                                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                  (@Finset.instMembership.{0} (Fin N)) A x)
                                              (@DFunLike.coe.{1, 1, 1}
                                                (Equiv.{1, 1}
                                                  (Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared)))
                                                  (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                    @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                      (@Finset.instMembership.{0} (Fin N)) A x))
                                                (Fin
                                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                      prepared)))
                                                (fun
                                                    (x :
                                                      Fin
                                                        (@List.length.{0}
                                                          BalancedAssortments.FixedSupportCostPoints.Product
                                                          (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                            prepared))) =>
                                                  @Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                    @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                      (@Finset.instMembership.{0} (Fin N)) A x)
                                                (@EquivLike.toFunLike.{1, 1, 1}
                                                  (Equiv.{1, 1}
                                                    (Fin
                                                      (@List.length.{0}
                                                        BalancedAssortments.FixedSupportCostPoints.Product
                                                        (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                          prepared)))
                                                    (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                      @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                        (@Finset.instMembership.{0} (Fin N)) A x))
                                                  (Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared)))
                                                  (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                    @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                      (@Finset.instMembership.{0} (Fin N)) A x)
                                                  (@Equiv.instEquivLike.{1, 1}
                                                    (Fin
                                                      (@List.length.{0}
                                                        BalancedAssortments.FixedSupportCostPoints.Product
                                                        (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                          prepared)))
                                                    (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                      @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                        (@Finset.instMembership.{0} (Fin N)) A x)))
                                                e j)))
                                        (fun
                                            (j :
                                              Fin
                                                (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                    prepared))) =>
                                          v
                                            (@Subtype.val.{1} (Fin N)
                                              (fun (x : Fin N) =>
                                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                  (@Finset.instMembership.{0} (Fin N)) A x)
                                              (@DFunLike.coe.{1, 1, 1}
                                                (Equiv.{1, 1}
                                                  (Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared)))
                                                  (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                    @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                      (@Finset.instMembership.{0} (Fin N)) A x))
                                                (Fin
                                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                      prepared)))
                                                (fun
                                                    (x :
                                                      Fin
                                                        (@List.length.{0}
                                                          BalancedAssortments.FixedSupportCostPoints.Product
                                                          (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                            prepared))) =>
                                                  @Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                    @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                      (@Finset.instMembership.{0} (Fin N)) A x)
                                                (@EquivLike.toFunLike.{1, 1, 1}
                                                  (Equiv.{1, 1}
                                                    (Fin
                                                      (@List.length.{0}
                                                        BalancedAssortments.FixedSupportCostPoints.Product
                                                        (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                          prepared)))
                                                    (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                      @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                        (@Finset.instMembership.{0} (Fin N)) A x))
                                                  (Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared)))
                                                  (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                    @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                      (@Finset.instMembership.{0} (Fin N)) A x)
                                                  (@Equiv.instEquivLike.{1, 1}
                                                    (Fin
                                                      (@List.length.{0}
                                                        BalancedAssortments.FixedSupportCostPoints.Product
                                                        (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                          prepared)))
                                                    (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                      @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                        (@Finset.instMembership.{0} (Fin N)) A x)))
                                                e j)))
                                        (BalancedAssortments.ComplexityTimeFractions.decode α)
                                        (BalancedAssortments.ComplexityTimeFractions.decode K) out p)
                                      (And
                                        (∀
                                          (x :
                                            Prod.{0, 0}
                                              (Fin
                                                (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                    prepared)))
                                              BalancedAssortments.FixedSupportCostRational.Fraction),
                                          @Membership.mem.{0, 0}
                                              (Prod.{0, 0}
                                                (Fin
                                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                      prepared)))
                                                BalancedAssortments.FixedSupportCostRational.Fraction)
                                              (List.{0}
                                                (Prod.{0, 0}
                                                  (Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared)))
                                                  BalancedAssortments.FixedSupportCostRational.Fraction))
                                              (@List.instMembership.{0}
                                                (Prod.{0, 0}
                                                  (Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared)))
                                                  BalancedAssortments.FixedSupportCostRational.Fraction))
                                              (@Prod.fst.{0, 0}
                                                (List.{0}
                                                  (Prod.{0, 0}
                                                    (Fin
                                                      (@List.length.{0}
                                                        BalancedAssortments.FixedSupportCostPoints.Product
                                                        (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                          prepared)))
                                                    BalancedAssortments.FixedSupportCostRational.Fraction))
                                                BalancedAssortments.FixedSupportCostRational.Fraction out)
                                              x →
                                            BalancedAssortments.ComplexityTimeFractions.Valid
                                              (@Prod.snd.{0, 0}
                                                (Fin
                                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                      prepared)))
                                                BalancedAssortments.FixedSupportCostRational.Fraction x))
                                        (And
                                          (BalancedAssortments.ComplexityTimeFractions.Valid
                                            (@Prod.snd.{0, 0}
                                              (List.{0}
                                                (Prod.{0, 0}
                                                  (Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared)))
                                                  BalancedAssortments.FixedSupportCostRational.Fraction))
                                              BalancedAssortments.FixedSupportCostRational.Fraction out))
                                          (@BalancedAssortments.FixedSupportAmbient.AmbientOptimal N A
                                            (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (r i))
                                            (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (v i))
                                            (@BalancedAssortments.FixedSupportAmbient.extendIndexed N
                                              (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                  prepared))
                                              A e
                                              fun
                                                (j :
                                                  Fin
                                                    (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                      (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                        prepared))) =>
                                              @Rat.cast.{0} Real Real.instRatCast
                                                (@BalancedAssortments.FixedSupportAlgorithm.candidateVector
                                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                      prepared))
                                                  (fun
                                                      (j :
                                                        Fin
                                                          (@List.length.{0}
                                                            BalancedAssortments.FixedSupportCostPoints.Product
                                                            (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                              prepared))) =>
                                                    r
                                                      (@Subtype.val.{1} (Fin N)
                                                        (fun (x : Fin N) =>
                                                          @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                            (@Finset.instMembership.{0} (Fin N)) A x)
                                                        (@DFunLike.coe.{1, 1, 1}
                                                          (Equiv.{1, 1}
                                                            (Fin
                                                              (@List.length.{0}
                                                                BalancedAssortments.FixedSupportCostPoints.Product
                                                                (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                  prepared)))
                                                            (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                (@Finset.instMembership.{0} (Fin N)) A x))
                                                          (Fin
                                                            (@List.length.{0}
                                                              BalancedAssortments.FixedSupportCostPoints.Product
                                                              (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                prepared)))
                                                          (fun
                                                              (x :
                                                                Fin
                                                                  (@List.length.{0}
                                                                    BalancedAssortments.FixedSupportCostPoints.Product
                                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                      prepared))) =>
                                                            @Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                (@Finset.instMembership.{0} (Fin N)) A x)
                                                          (@EquivLike.toFunLike.{1, 1, 1}
                                                            (Equiv.{1, 1}
                                                              (Fin
                                                                (@List.length.{0}
                                                                  BalancedAssortments.FixedSupportCostPoints.Product
                                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                    prepared)))
                                                              (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                  (@Finset.instMembership.{0} (Fin N)) A x))
                                                            (Fin
                                                              (@List.length.{0}
                                                                BalancedAssortments.FixedSupportCostPoints.Product
                                                                (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                  prepared)))
                                                            (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                (@Finset.instMembership.{0} (Fin N)) A x)
                                                            (@Equiv.instEquivLike.{1, 1}
                                                              (Fin
                                                                (@List.length.{0}
                                                                  BalancedAssortments.FixedSupportCostPoints.Product
                                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                    prepared)))
                                                              (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                  (@Finset.instMembership.{0} (Fin N)) A x)))
                                                          e j)))
                                                  (fun
                                                      (j :
                                                        Fin
                                                          (@List.length.{0}
                                                            BalancedAssortments.FixedSupportCostPoints.Product
                                                            (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                              prepared))) =>
                                                    v
                                                      (@Subtype.val.{1} (Fin N)
                                                        (fun (x : Fin N) =>
                                                          @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                            (@Finset.instMembership.{0} (Fin N)) A x)
                                                        (@DFunLike.coe.{1, 1, 1}
                                                          (Equiv.{1, 1}
                                                            (Fin
                                                              (@List.length.{0}
                                                                BalancedAssortments.FixedSupportCostPoints.Product
                                                                (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                  prepared)))
                                                            (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                (@Finset.instMembership.{0} (Fin N)) A x))
                                                          (Fin
                                                            (@List.length.{0}
                                                              BalancedAssortments.FixedSupportCostPoints.Product
                                                              (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                prepared)))
                                                          (fun
                                                              (x :
                                                                Fin
                                                                  (@List.length.{0}
                                                                    BalancedAssortments.FixedSupportCostPoints.Product
                                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                      prepared))) =>
                                                            @Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                (@Finset.instMembership.{0} (Fin N)) A x)
                                                          (@EquivLike.toFunLike.{1, 1, 1}
                                                            (Equiv.{1, 1}
                                                              (Fin
                                                                (@List.length.{0}
                                                                  BalancedAssortments.FixedSupportCostPoints.Product
                                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                    prepared)))
                                                              (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                  (@Finset.instMembership.{0} (Fin N)) A x))
                                                            (Fin
                                                              (@List.length.{0}
                                                                BalancedAssortments.FixedSupportCostPoints.Product
                                                                (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                  prepared)))
                                                            (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                              @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                (@Finset.instMembership.{0} (Fin N)) A x)
                                                            (@Equiv.instEquivLike.{1, 1}
                                                              (Fin
                                                                (@List.length.{0}
                                                                  BalancedAssortments.FixedSupportCostPoints.Product
                                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                    prepared)))
                                                              (@Subtype.{1} (Fin N) fun (x : Fin N) =>
                                                                @Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                                                  (@Finset.instMembership.{0} (Fin N)) A x)))
                                                          e j)))
                                                  (BalancedAssortments.ComplexityTimeFractions.decode α)
                                                  (BalancedAssortments.ComplexityTimeFractions.decode K) p j))
                                            (@Rat.cast.{0} Real Real.instRatCast
                                              (BalancedAssortments.ComplexityTimeFractions.decode α))
                                            (@Rat.cast.{0} Real Real.instRatCast
                                              (BalancedAssortments.ComplexityTimeFractions.decode K))
                                            (@Rat.cast.{0} Real Real.instRatCast
                                              (BalancedAssortments.ComplexityTimeFractions.decode
                                                (@Prod.snd.{0, 0}
                                                  (List.{0}
                                                    (Prod.{0, 0}
                                                      (Fin
                                                        (@List.length.{0}
                                                          BalancedAssortments.FixedSupportCostPoints.Product
                                                          (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                            prepared)))
                                                      BalancedAssortments.FixedSupportCostRational.Fraction))
                                                  BalancedAssortments.FixedSupportCostRational.Fraction out))))))))
                          (@LE.le.{0} Nat instLENat
                            (@Prod.snd.{0, 0}
                              (Option.{0} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult) Nat
                              (BalancedAssortments.FixedSupportAmbientPreprocess.runAmbient α K
                                (@List.ofFn.{0} BalancedAssortments.FixedSupportCostPoints.Product N data)
                                (@List.ofFn.{0} Bool N mask)))
                            (@Polynomial.eval.{0} Nat Nat.instSemiring
                              (@List.length.{0} Bool
                                (BalancedAssortments.FixedSupportAmbientPreprocess.serializedAmbient α K
                                  (@List.ofFn.{0} BalancedAssortments.FixedSupportCostPoints.Product N data)
                                  (@List.ofFn.{0} Bool N mask)))
                              P))) := by
  sorry

/-- P4: `BalancedAssortments.FixedSupportAmbient.runAmbient_original_policy`. -/
theorem claim_014 :
  (∀ {N K : Nat} (A : Finset.{0} (Fin N)) (hA : @Finset.Nonempty.{0} (Fin N) A)
  (data : Fin N → BalancedAssortments.FixedSupportCostPoints.Product) (mask : Fin N → Bool) (r v : Fin N → Rat)
  (α κ : BalancedAssortments.FixedSupportCostRational.Fraction)
  (hm :
    ∀ (i : Fin N),
      Iff (@Eq.{1} Bool (mask i) Bool.true)
        (@Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N)) (@Finset.instMembership.{0} (Fin N)) A i))
  (hd : ∀ (i : Fin N), BalancedAssortments.FixedSupportCostPoints.Product.Valid (data i))
  (hr : ∀ (i : Fin N), @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (r i))
  (hv : ∀ (i : Fin N), @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (v i))
  (hα : BalancedAssortments.ComplexityTimeFractions.Valid α) (hκ : BalancedAssortments.ComplexityTimeFractions.Valid κ)
  (hαpos :
    @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (BalancedAssortments.ComplexityTimeFractions.decode α))
  (hα1 :
    @LE.le.{0} Rat Rat.instLE (BalancedAssortments.ComplexityTimeFractions.decode α)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (hKpos :
    @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (BalancedAssortments.ComplexityTimeFractions.decode κ))
  (hK : @Eq.{1} Rat (BalancedAssortments.ComplexityTimeFractions.decode κ) (@Nat.cast.{0} Rat Rat.instNatCast K))
  (hdata :
    ∀ (i : Fin N),
      And
        (@Eq.{1} Rat
          (BalancedAssortments.ComplexityTimeFractions.decode
            (@Prod.fst.{0, 0} BalancedAssortments.FixedSupportCostRational.Fraction
              BalancedAssortments.FixedSupportCostRational.Fraction (data i)))
          (r i))
        (@Eq.{1} Rat
          (BalancedAssortments.ComplexityTimeFractions.decode
            (@Prod.snd.{0, 0} BalancedAssortments.FixedSupportCostRational.Fraction
              BalancedAssortments.FixedSupportCostRational.Fraction (data i)))
          (v i))),
  @Exists.{1} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult
    fun (result : BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult) =>
    And
      (@Eq.{1} (Option.{0} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult)
        (@Prod.fst.{0, 0} (Option.{0} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult) Nat
          (BalancedAssortments.FixedSupportAmbientPreprocess.runAmbient α κ
            (@List.ofFn.{0} BalancedAssortments.FixedSupportCostPoints.Product N data) (@List.ofFn.{0} Bool N mask)))
        (@Option.some.{0} BalancedAssortments.FixedSupportAmbientPreprocess.AmbientResult result))
      (@Exists.{1} Nat fun (m : Nat) =>
        And
          (@LE.le.{0} Nat instLENat m
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Exists.{1} (Fin m → Finset.{0} (Fin N)) fun (S : Fin m → Finset.{0} (Fin N)) =>
            @Exists.{1} (Fin m → Real) fun (q : Fin m → Real) =>
              And (@BalancedAssortments.Sales.Distribution.{0} (Fin m) (Fin.fintype m) q)
                (And (∀ (a : Fin m), @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin N) (S a)) K)
                  (And
                    (@BalancedAssortments.Sales.Balanced.{0} (Fin N)
                      (@Rat.cast.{0} Real Real.instRatCast (BalancedAssortments.ComplexityTimeFractions.decode α))
                      (@BalancedAssortments.Sales.sales.{0, 0} (Fin N) (Fin m) (instDecidableEqFin N) (Fin.fintype m)
                        (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (v i)) S q))
                    (And
                      (∀ (i : Fin N),
                        Iff
                          (@LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@BalancedAssortments.Sales.sales.{0, 0} (Fin N) (Fin m) (instDecidableEqFin N)
                              (Fin.fintype m) (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (v i)) S q i))
                          (@Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N)) (@Finset.instMembership.{0} (Fin N)) A
                            i))
                      (And
                        (@Eq.{1} Real
                          (@BalancedAssortments.Sales.revenue.{0} (Fin N) (Fin.fintype N)
                            (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (r i))
                            (@BalancedAssortments.Sales.sales.{0, 0} (Fin N) (Fin m) (instDecidableEqFin N)
                              (Fin.fintype m) (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (v i)) S q))
                          (@Rat.cast.{0} Real Real.instRatCast
                            (BalancedAssortments.ComplexityTimeFractions.decode
                              (@Prod.snd.{0, 0}
                                (List.{0}
                                  (Prod.{0, 0}
                                    (Fin
                                      (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                        (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                          (@Sigma.fst.{0, 0} BalancedAssortments.FixedSupportAmbientPreprocess.Prepared
                                            (fun (out : BalancedAssortments.FixedSupportAmbientPreprocess.Prepared) =>
                                              BalancedAssortments.FixedSupportCostMax.Result.{0}
                                                (Fin
                                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                      out))))
                                            result))))
                                    BalancedAssortments.FixedSupportCostRational.Fraction))
                                BalancedAssortments.FixedSupportCostRational.Fraction
                                (@Sigma.snd.{0, 0} BalancedAssortments.FixedSupportAmbientPreprocess.Prepared
                                  (fun (out : BalancedAssortments.FixedSupportAmbientPreprocess.Prepared) =>
                                    BalancedAssortments.FixedSupportCostMax.Result.{0}
                                      (Fin
                                        (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                          (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products out))))
                                  result)))))
                        (∀ {J : Type} [inst : Fintype.{0} J] (T : J → Finset.{0} (Fin N)) (p : J → Real),
                          @BalancedAssortments.Sales.Distribution.{0} J inst p →
                            (∀ (a : J), @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin N) (T a)) K) →
                              @BalancedAssortments.Sales.Balanced.{0} (Fin N)
                                  (@Rat.cast.{0} Real Real.instRatCast
                                    (BalancedAssortments.ComplexityTimeFractions.decode α))
                                  (@BalancedAssortments.Sales.sales.{0, 0} (Fin N) J (instDecidableEqFin N) inst
                                    (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (v i)) T p) →
                                (∀ (i : Fin N),
                                    Iff
                                      (@LT.lt.{0} Real Real.instLT
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                        (@BalancedAssortments.Sales.sales.{0, 0} (Fin N) J (instDecidableEqFin N) inst
                                          (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (v i)) T p i))
                                      (@Membership.mem.{0, 0} (Fin N) (Finset.{0} (Fin N))
                                        (@Finset.instMembership.{0} (Fin N)) A i)) →
                                  @LE.le.{0} Real Real.instLE
                                    (@BalancedAssortments.Sales.revenue.{0} (Fin N) (Fin.fintype N)
                                      (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (r i))
                                      (@BalancedAssortments.Sales.sales.{0, 0} (Fin N) J (instDecidableEqFin N) inst
                                        (fun (i : Fin N) => @Rat.cast.{0} Real Real.instRatCast (v i)) T p))
                                    (@Rat.cast.{0} Real Real.instRatCast
                                      (BalancedAssortments.ComplexityTimeFractions.decode
                                        (@Prod.snd.{0, 0}
                                          (List.{0}
                                            (Prod.{0, 0}
                                              (Fin
                                                (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                  (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                    (@Sigma.fst.{0, 0}
                                                      BalancedAssortments.FixedSupportAmbientPreprocess.Prepared
                                                      (fun
                                                          (out :
                                                            BalancedAssortments.FixedSupportAmbientPreprocess.Prepared) =>
                                                        BalancedAssortments.FixedSupportCostMax.Result.{0}
                                                          (Fin
                                                            (@List.length.{0}
                                                              BalancedAssortments.FixedSupportCostPoints.Product
                                                              (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                                out))))
                                                      result))))
                                              BalancedAssortments.FixedSupportCostRational.Fraction))
                                          BalancedAssortments.FixedSupportCostRational.Fraction
                                          (@Sigma.snd.{0, 0} BalancedAssortments.FixedSupportAmbientPreprocess.Prepared
                                            (fun (out : BalancedAssortments.FixedSupportAmbientPreprocess.Prepared) =>
                                              BalancedAssortments.FixedSupportCostMax.Result.{0}
                                                (Fin
                                                  (@List.length.{0} BalancedAssortments.FixedSupportCostPoints.Product
                                                    (BalancedAssortments.FixedSupportAmbientPreprocess.Prepared.products
                                                      out))))
                                            result)))))))))))) := by
  sorry

/-- P4: `BalancedAssortments.FixedSupportCostProgram.binary_fixed_support_solver`. -/
theorem claim_015 :
  (∀ {n B : Nat} (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (r v : Fin n → Rat) (ps : List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product))
  (α K : BalancedAssortments.FixedSupportCostRational.Fraction)
  (hlabels :
    @Eq.{1} (List.{0} (Fin n))
      (@List.map.{0, 0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product) (Fin n)
        (@Prod.fst.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product) ps)
      (List.finRange n))
  (hp :
    ∀ (p : Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product),
      @Membership.mem.{0, 0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product)
          (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product))
          (@List.instMembership.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product)) ps p →
        BalancedAssortments.FixedSupportCostPoints.Product.Valid
          (@Prod.snd.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product p))
  (hr : ∀ (i : Fin n), @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (r i))
  (hv : ∀ (i : Fin n), @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (v i))
  (hα : BalancedAssortments.ComplexityTimeFractions.Valid α) (hK : BalancedAssortments.ComplexityTimeFractions.Valid K)
  (hαpos :
    @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (BalancedAssortments.ComplexityTimeFractions.decode α))
  (hα1 :
    @LE.le.{0} Rat Rat.instLE (BalancedAssortments.ComplexityTimeFractions.decode α)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (hKpos :
    @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (BalancedAssortments.ComplexityTimeFractions.decode K))
  (hdata :
    ∀ (p : Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product),
      @Membership.mem.{0, 0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product)
          (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product))
          (@List.instMembership.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product)) ps p →
        And
          (@Eq.{1} Rat
            (BalancedAssortments.ComplexityTimeFractions.decode
              (@Prod.fst.{0, 0} BalancedAssortments.FixedSupportCostRational.Fraction
                BalancedAssortments.FixedSupportCostRational.Fraction
                (@Prod.snd.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product p)))
            (r (@Prod.fst.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product p)))
          (@Eq.{1} Rat
            (BalancedAssortments.ComplexityTimeFractions.decode
              (@Prod.snd.{0, 0} BalancedAssortments.FixedSupportCostRational.Fraction
                BalancedAssortments.FixedSupportCostRational.Fraction
                (@Prod.snd.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product p)))
            (v (@Prod.fst.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product p))))
  (hαw : @LE.le.{0} Nat instLENat (BalancedAssortments.ComplexityTimeFractions.width α) B)
  (hKw : @LE.le.{0} Nat instLENat (BalancedAssortments.ComplexityTimeFractions.width K) B)
  (hpw :
    ∀ (p : Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product),
      @Membership.mem.{0, 0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product)
          (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product))
          (@List.instMembership.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product)) ps p →
        BalancedAssortments.FixedSupportCostPoints.Product.Width
          (@Prod.snd.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostPoints.Product p) B),
  @Exists.{1} (BalancedAssortments.FixedSupportCostMax.Result.{0} (Fin n))
    fun (out : BalancedAssortments.FixedSupportCostMax.Result.{0} (Fin n)) =>
    @Exists.{1} (Prod.{0, 0} Rat Rat) fun (p : Prod.{0, 0} Rat Rat) =>
      And
        (@Eq.{1} (Option.{0} (BalancedAssortments.FixedSupportCostMax.Result.{0} (Fin n)))
          (@Prod.fst.{0, 0} (Option.{0} (BalancedAssortments.FixedSupportCostMax.Result.{0} (Fin n))) Nat
            (@BalancedAssortments.FixedSupportCostProgram.runBits.{0} (Fin n) α K ps))
          (@Option.some.{0} (BalancedAssortments.FixedSupportCostMax.Result.{0} (Fin n)) out))
        (And
          (@BalancedAssortments.FixedSupportCostProgram.Realizes n r v
            (BalancedAssortments.ComplexityTimeFractions.decode α)
            (BalancedAssortments.ComplexityTimeFractions.decode K) out p)
          (And
            (@Eq.{1} Nat
              (@List.length.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction)
                (@Prod.fst.{0, 0} (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction))
                  BalancedAssortments.FixedSupportCostRational.Fraction out))
              n)
            (And
              (∀ (x : Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction),
                @Membership.mem.{0, 0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction)
                    (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction))
                    (@List.instMembership.{0}
                      (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction))
                    (@Prod.fst.{0, 0}
                      (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction))
                      BalancedAssortments.FixedSupportCostRational.Fraction out)
                    x →
                  And
                    (BalancedAssortments.ComplexityTimeFractions.Valid
                      (@Prod.snd.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction x))
                    (And
                      (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                        (BalancedAssortments.ComplexityTimeFractions.decode
                          (@Prod.snd.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction x)))
                      (@LE.le.{0} Nat instLENat
                        (BalancedAssortments.ComplexityTimeFractions.width
                          (@Prod.snd.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction x))
                        (BalancedAssortments.FixedSupportCostProgram.outputVectorWidth n B))))
              (And
                (BalancedAssortments.ComplexityTimeFractions.Valid
                  (@Prod.snd.{0, 0}
                    (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction))
                    BalancedAssortments.FixedSupportCostRational.Fraction out))
                (And
                  (@LE.le.{0} Nat instLENat
                    (BalancedAssortments.ComplexityTimeFractions.width
                      (@Prod.snd.{0, 0}
                        (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction))
                        BalancedAssortments.FixedSupportCostRational.Fraction out))
                    (BalancedAssortments.FixedSupportCostProgram.outputObjectiveWidth n B))
                  (And
                    (@BalancedAssortments.FixedSupportReal.Feasible.{0} (Fin n) (Fin.fintype n)
                      (fun (i : Fin n) => @Rat.cast.{0} Real Real.instRatCast (v i))
                      (@Rat.cast.{0} Real Real.instRatCast (BalancedAssortments.ComplexityTimeFractions.decode α))
                      (@Rat.cast.{0} Real Real.instRatCast (BalancedAssortments.ComplexityTimeFractions.decode K))
                      fun (i : Fin n) =>
                      @Rat.cast.{0} Real Real.instRatCast
                        (@BalancedAssortments.FixedSupportAlgorithm.candidateVector n r v
                          (BalancedAssortments.ComplexityTimeFractions.decode α)
                          (BalancedAssortments.ComplexityTimeFractions.decode K) p i))
                    (And
                      (∀ (w : Fin n → Real),
                        @BalancedAssortments.FixedSupportReal.Feasible.{0} (Fin n) (Fin.fintype n)
                            (fun (i : Fin n) => @Rat.cast.{0} Real Real.instRatCast (v i))
                            (@Rat.cast.{0} Real Real.instRatCast (BalancedAssortments.ComplexityTimeFractions.decode α))
                            (@Rat.cast.{0} Real Real.instRatCast (BalancedAssortments.ComplexityTimeFractions.decode K))
                            w →
                          @LE.le.{0} Real Real.instLE
                            (@BalancedAssortments.FixedSupportReal.revenue.{0} (Fin n) (Fin.fintype n)
                              (fun (i : Fin n) => @Rat.cast.{0} Real Real.instRatCast (r i)) w)
                            (@Rat.cast.{0} Real Real.instRatCast
                              (BalancedAssortments.ComplexityTimeFractions.decode
                                (@Prod.snd.{0, 0}
                                  (List.{0} (Prod.{0, 0} (Fin n) BalancedAssortments.FixedSupportCostRational.Fraction))
                                  BalancedAssortments.FixedSupportCostRational.Fraction out))))
                      (@LE.le.{0} Nat instLENat
                        (@Prod.snd.{0, 0} (Option.{0} (BalancedAssortments.FixedSupportCostMax.Result.{0} (Fin n))) Nat
                          (@BalancedAssortments.FixedSupportCostProgram.runBits.{0} (Fin n) α K ps))
                        (BalancedAssortments.FixedSupportCostProgram.runCost n B)))))))))) := by
  sorry

/-- C5: `BalancedAssortments.FixedSupportReal.alpha_one_exact_maximum`. -/
theorem claim_016.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : Nonempty.{u_1 + 1} ι] (v r : ι → Real) (K : Real)
  (hv :
    ∀ (i : ι),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  (hr :
    ∀ (i : ι),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (r i))
  (hK : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K),
  And
    (@BalancedAssortments.FixedSupportReal.Feasible.{u_1} ι inst v
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K fun (x : ι) =>
      @BalancedAssortments.FixedSupportReal.commonOptimum.{u_1} ι inst inst_1 v K)
    (And
      (∀ (i : ι),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@BalancedAssortments.FixedSupportReal.commonOptimum.{u_1} ι inst inst_1 v K))
      (∀ (w : ι → Real),
        @BalancedAssortments.FixedSupportReal.Feasible.{u_1} ι inst v
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K w →
          @LE.le.{0} Real Real.instLE (@BalancedAssortments.FixedSupportReal.revenue.{u_1} ι inst r w)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@BalancedAssortments.FixedSupportReal.commonOptimum.{u_1} ι inst inst_1 v K)
                (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (i : ι) => r i))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                  (@BalancedAssortments.FixedSupportReal.commonOptimum.{u_1} ι inst inst_1 v K))))))) := by
  sorry

/-- C5: `BalancedAssortments.FixedSupport.alpha_one_exact_maximum`. -/
theorem claim_017.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : Nonempty.{u_1 + 1} ι] (v r : ι → Rat) (K : Rat)
  (hv : ∀ (i : ι), @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (v i))
  (hr : ∀ (i : ι), @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (r i))
  (hK : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) K),
  And
    (@BalancedAssortments.FixedSupport.Feasible.{u_1} ι inst v
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) K fun (x : ι) =>
      @BalancedAssortments.FixedSupport.commonOptimum.{u_1} ι inst inst_1 v K)
    (And
      (∀ (i : ι),
        @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@BalancedAssortments.FixedSupport.commonOptimum.{u_1} ι inst inst_1 v K))
      (∀ (w : ι → Rat),
        @BalancedAssortments.FixedSupport.Feasible.{u_1} ι inst v
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) K w →
          @LE.le.{0} Rat Rat.instLE (@BalancedAssortments.FixedSupport.revenue.{u_1} ι inst r w)
            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                (@BalancedAssortments.FixedSupport.commonOptimum.{u_1} ι inst inst_1 v K)
                (@Finset.sum.{u_1, 0} ι Rat Rat.addCommMonoid (@Finset.univ.{u_1} ι inst) fun (i : ι) => r i))
              (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                  (@Nat.cast.{0} Rat Rat.instNatCast (@Fintype.card.{u_1} ι inst))
                  (@BalancedAssortments.FixedSupport.commonOptimum.{u_1} ι inst inst_1 v K))))))) := by
  sorry

/-- P6: `BalancedAssortments.Counterexample.shared_global_optimum`. -/
theorem claim_018 :
  (∀ (w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
  (hc :
    @BalancedAssortments.Sales.CompactFeasible.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      BalancedAssortments.Counterexample.attractions w (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hb :
    @BalancedAssortments.Sales.Balanced.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 6)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
      w),
  @LE.le.{0} Real Real.instLE
    (@BalancedAssortments.Sales.objective.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      BalancedAssortments.Counterexample.prices w)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 928)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 928) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 927) (instOfNatNat (nat_lit 927)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 926) (instOfNatNat (nat_lit 926)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 15)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 15) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))))))) := by
  sorry

/-- P6: `BalancedAssortments.Counterexample.shared_unique_optimizer`. -/
theorem claim_019 :
  (∀ (w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
  (hc :
    @BalancedAssortments.Sales.CompactFeasible.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      BalancedAssortments.Counterexample.attractions w (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hb :
    @BalancedAssortments.Sales.Balanced.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 6)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
      w)
  (he :
    @Eq.{1} Real
      (@BalancedAssortments.Sales.objective.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        BalancedAssortments.Counterexample.prices w)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 928)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 928) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 927) (instOfNatNat (nat_lit 927)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 926) (instOfNatNat (nat_lit 926)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 15)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 15) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))))))),
  @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real) w
    (BalancedAssortments.Counterexample.vector
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 12)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))))))) := by
  sorry

/-- P6: `BalancedAssortments.Counterexample.original_policy_bound`. -/
theorem claim_020.{u_1} :
  (∀ {A : Type u_1} [inst : Fintype.{u_1} A]
  (S : A → Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) (q : A → Real)
  (hq : @BalancedAssortments.Sales.Distribution.{u_1} A inst q)
  (hK :
    ∀ (a : A),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (S a))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hb :
    @BalancedAssortments.Sales.Balanced.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 6)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
      (@BalancedAssortments.Sales.sales.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) A
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) inst
        BalancedAssortments.Counterexample.attractions S q)),
  @LE.le.{0} Real Real.instLE
    (@BalancedAssortments.Sales.revenue.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      BalancedAssortments.Counterexample.prices
      (@BalancedAssortments.Sales.sales.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) A
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) inst
        BalancedAssortments.Counterexample.attractions S q))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 928)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 928) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 927) (instOfNatNat (nat_lit 927)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 926) (instOfNatNat (nat_lit 926)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 15)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 15) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))))))) := by
  sorry

/-- P6: `BalancedAssortments.Counterexample.global_bound`. -/
theorem claim_021 :
  (∀ {a b c : Real} (h : BalancedAssortments.Counterexample.Feasible a b c),
  @LE.le.{0} Real Real.instLE (BalancedAssortments.Counterexample.revenue a b c)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 928)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 928) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 927) (instOfNatNat (nat_lit 927)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 926) (instOfNatNat (nat_lit 926)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 15)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 15) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))))))) := by
  sorry

/-- P6: `BalancedAssortments.Counterexample.unique_optimizer`. -/
theorem claim_022 :
  (∀ {a b c : Real} (h : BalancedAssortments.Counterexample.Feasible a b c)
  (heq :
    @Eq.{1} Real (BalancedAssortments.Counterexample.revenue a b c)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 928)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 928) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 927) (instOfNatNat (nat_lit 927)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 926) (instOfNatNat (nat_lit 926)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 15)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 15) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))))))),
  And (@Eq.{1} Real a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (And
      (@Eq.{1} Real b
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@Eq.{1} Real c
        (@OfNat.ofNat.{0} Real (nat_lit 12)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))))) := by
  sorry

/-- P6: `BalancedAssortments.Counterexample.appendix_table_attainment`. -/
theorem claim_023 :
  (And
  (And
    (BalancedAssortments.Counterexample.Feasible
      (@OfNat.ofNat.{0} Real (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@Eq.{1} Real
      (BalancedAssortments.Counterexample.revenue
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 195)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 195) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 193) (instOfNatNat (nat_lit 193)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
  (And
    (And
      (BalancedAssortments.Counterexample.Feasible
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@Eq.{1} Real
        (BalancedAssortments.Counterexample.revenue
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 160)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 160) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 159) (instOfNatNat (nat_lit 159)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
    (And
      (And
        (BalancedAssortments.Counterexample.Feasible
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 14)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))))
        (@Eq.{1} Real
          (BalancedAssortments.Counterexample.revenue
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 14)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 896)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 896) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 895) (instOfNatNat (nat_lit 895)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 894) (instOfNatNat (nat_lit 894)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 15)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 15) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))))))))
      (And
        (And
          (BalancedAssortments.Counterexample.Feasible
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@Eq.{1} Real
            (BalancedAssortments.Counterexample.revenue
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 355)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 355) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 354) (instOfNatNat (nat_lit 354)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 353) (instOfNatNat (nat_lit 353)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 6)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
        (And
          (BalancedAssortments.Counterexample.Feasible
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 14)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))))
          (@Eq.{1} Real
            (BalancedAssortments.Counterexample.revenue
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@OfNat.ofNat.{0} Real (nat_lit 14)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1091)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 1091) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1090) (instOfNatNat (nat_lit 1090)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1089) (instOfNatNat (nat_lit 1089)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 18)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 18) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))))))))))) := by
  sorry

/-- P6: `BalancedAssortments.Counterexample.optimal_support_not_rectangle`. -/
theorem claim_024 :
  (Not
  (@Exists.{1} Real fun (rbar : Real) =>
    @Exists.{1} Real fun (vbar : Real) =>
      And
        (Not
          (And
            (@LE.le.{0} Real Real.instLE rbar
              (@OfNat.ofNat.{0} Real (nat_lit 65)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 65) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63))))))))
            (@LE.le.{0} Real Real.instLE vbar
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
        (And
          (And
            (@LE.le.{0} Real Real.instLE rbar
              (@OfNat.ofNat.{0} Real (nat_lit 80)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
            (@LE.le.{0} Real Real.instLE vbar
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          (And
            (@LE.le.{0} Real Real.instLE rbar
              (@OfNat.ofNat.{0} Real (nat_lit 64)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62))))))))
            (@LE.le.{0} Real Real.instLE vbar
              (@OfNat.ofNat.{0} Real (nat_lit 14)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))))))) := by
  sorry

/-- L7: `BalancedAssortments.Optimization.scale_range`. -/
theorem claim_025.{u_1} :
  (∀ {I : Type u_1} [inst : Fintype.{u_1} I] [Nonempty.{u_1 + 1} I] (r v : I → Real)
  (hr :
    ∀ (i : I),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (r i))
  (hv :
    ∀ (i : I),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  {α K : Real}
  (hα : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α)
  (hα1 : @LE.le.{0} Real Real.instLE α (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hK : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K),
  @Exists.{u_1 + 1} (I → Real) fun (w : I → Real) =>
    @Exists.{u_1 + 1} I fun (imin : I) =>
      @Exists.{u_1 + 1} I fun (imaxv : I) =>
        @Exists.{u_1 + 1} I fun (imaxw : I) =>
          And (@BalancedAssortments.Optimization.feasible.{u_1} I inst v α K w)
            (And
              (∀ (u : I → Real),
                @BalancedAssortments.Optimization.feasible.{u_1} I inst v α K u →
                  @LE.le.{0} Real Real.instLE (@BalancedAssortments.Optimization.revenue.{u_1} I inst r u)
                    (@BalancedAssortments.Optimization.revenue.{u_1} I inst r w))
              (And (∀ (i : I), @LE.le.{0} Real Real.instLE (v imin) (v i))
                (And (∀ (i : I), @LE.le.{0} Real Real.instLE (v i) (v imaxv))
                  (And (∀ (i : I), @LE.le.{0} Real Real.instLE (w i) (w imaxw))
                    (And
                      (@LE.le.{0} Real Real.instLE
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) α (v imin))
                          (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} I inst)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) α (w imaxw)))
                      (@LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) α (w imaxw))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) α (v imaxv))))))))) := by
  sorry

/-- L7: `BalancedAssortments.Optimization.optimum_exists`. -/
theorem claim_026.{u_1} :
  (∀ {I : Type u_1} [inst : Fintype.{u_1} I] (r v : I → Real)
  (hv :
    ∀ (i : I),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  (α K : Real)
  (hK : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K),
  @Exists.{u_1 + 1} (I → Real) fun (w : I → Real) =>
    And (@BalancedAssortments.Optimization.feasible.{u_1} I inst v α K w)
      (∀ (u : I → Real),
        @BalancedAssortments.Optimization.feasible.{u_1} I inst v α K u →
          @LE.le.{0} Real Real.instLE (@BalancedAssortments.Optimization.revenue.{u_1} I inst r u)
            (@BalancedAssortments.Optimization.revenue.{u_1} I inst r w))) := by
  sorry

/-- L7: `BalancedAssortments.Optimization.optimum_positive`. -/
theorem claim_027.{u_1} :
  (∀ {I : Type u_1} [inst : Fintype.{u_1} I] [Nonempty.{u_1 + 1} I] (r v : I → Real)
  (hr :
    ∀ (i : I),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (r i))
  (hv :
    ∀ (i : I),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  {α K : Real}
  (hα : @LE.le.{0} Real Real.instLE α (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hK : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K)
  {w : I → Real}
  (hmax :
    ∀ (u : I → Real),
      @BalancedAssortments.Optimization.feasible.{u_1} I inst v α K u →
        @LE.le.{0} Real Real.instLE (@BalancedAssortments.Optimization.revenue.{u_1} I inst r u)
          (@BalancedAssortments.Optimization.revenue.{u_1} I inst r w)),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@BalancedAssortments.Optimization.revenue.{u_1} I inst r w)) := by
  sorry

/-- L8: `BalancedAssortments.ApproximationDiscretization.scale_discretization`. -/
theorem claim_028.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] (r w : ι → Real) (v : ι → Rat) {a cap δ α : Rat} {τstar : Real}
  (ha : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) a)
  (hδ : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) δ)
  (hα : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) α)
  (hslo : @LE.le.{0} Real Real.instLE (@Rat.cast.{0} Real Real.instRatCast a) τstar)
  (hshi : @LE.le.{0} Real Real.instLE τstar (@Rat.cast.{0} Real Real.instRatCast cap))
  (hr :
    ∀ (i : ι),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (r i))
  (hwcap : ∀ (i : ι), @LE.le.{0} Real Real.instLE (w i) (@Rat.cast.{0} Real Real.instRatCast (v i)))
  (hwband :
    ∀ (i : ι),
      Or (@Eq.{1} Real (w i) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (And (@LE.le.{0} Real Real.instLE τstar (w i))
          (@LE.le.{0} Real Real.instLE (w i)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) τstar
              (@Rat.cast.{0} Real Real.instRatCast α))))),
  @Exists.{1} Rat fun (τ : Rat) =>
    And
      (@Membership.mem.{0, 0} Rat (List.{0} Rat) (@List.instMembership.{0} Rat)
        (BalancedAssortments.Grids.geometricGrid a δ cap (BalancedAssortments.GridBounds.gridHorizon a δ cap)) τ)
      (@Exists.{u_1 + 1} (ι → Rat) fun (y : ι → Rat) =>
        And
          (∀ (i : ι),
            @Membership.mem.{0, 0} Rat (List.{0} Rat) (@List.instMembership.{0} Rat)
              (BalancedAssortments.Grids.productOptions τ δ α (v i)
                (BalancedAssortments.GridBounds.gridHorizon τ δ
                  (@Min.min.{0} Rat Rat.instInf (v i)
                    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) τ α))))
              (y i))
          (And (∀ (i : ι), @LE.le.{0} Real Real.instLE (@Rat.cast.{0} Real Real.instRatCast (y i)) (w i))
            (@LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (BalancedAssortments.Approximation.revenue
                  (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (i : ι) =>
                    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (r i) (w i))
                  (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (i : ι) => w i))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Rat.cast.{0} Real Real.instRatCast δ))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (BalancedAssortments.Approximation.revenue
                (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (i : ι) =>
                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (r i)
                    (@Rat.cast.{0} Real Real.instRatCast (y i)))
                (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{u_1} ι inst) fun (i : ι) =>
                  @Rat.cast.{0} Real Real.instRatCast (y i))))))) := by
  sorry

/-- L8: `BalancedAssortments.FPTAS.discrete_candidate_exists`. -/
theorem claim_029 :
  (∀ {n : Nat} (d : BalancedAssortments.FPTAS.Input n) (hd : @BalancedAssortments.FPTAS.Valid n d) {δ : Rat}
  (hδ : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) δ),
  @Exists.{1}
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real)
    fun
      (w :
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real) =>
    And
      (@BalancedAssortments.Optimization.feasible.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (fun
            (i :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.v n d i))
        (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.α n d))
        (@Nat.cast.{0} Real Real.instNatCast (@BalancedAssortments.FPTAS.Input.K n d)) w)
      (And
        (∀
          (u :
            Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real),
          @BalancedAssortments.Optimization.feasible.{0}
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (fun
                  (i :
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.v n d i))
              (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.α n d))
              (@Nat.cast.{0} Real Real.instNatCast (@BalancedAssortments.FPTAS.Input.K n d)) u →
            @LE.le.{0} Real Real.instLE
              (@BalancedAssortments.Optimization.revenue.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (fun
                    (i :
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
                u)
              (@BalancedAssortments.Optimization.revenue.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (fun
                    (i :
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
                w))
        (@Exists.{1} Rat fun (τ : Rat) =>
          And
            (@Membership.mem.{0, 0} Rat (List.{0} Rat) (@List.instMembership.{0} Rat)
              (@BalancedAssortments.FPTAS.scales n d δ) τ)
            (@Exists.{1}
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Rat)
              fun
                (y :
                  Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Rat) =>
              And
                (∀
                  (i :
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
                  @Membership.mem.{0, 0} Rat (List.{0} Rat) (@List.instMembership.{0} Rat)
                    (BalancedAssortments.Grids.productOptions τ δ (@BalancedAssortments.FPTAS.Input.α n d)
                      (@BalancedAssortments.FPTAS.Input.v n d i)
                      (BalancedAssortments.GridBounds.gridHorizon τ δ
                        (@Min.min.{0} Rat Rat.instInf (@BalancedAssortments.FPTAS.Input.v n d i)
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) τ
                            (@BalancedAssortments.FPTAS.Input.α n d)))))
                    (y i))
                (And (@BalancedAssortments.FPTAS.Feasible n d y)
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@BalancedAssortments.Optimization.revenue.{0}
                        (Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin.fintype
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (fun
                            (i :
                              Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                          @Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.Input.r n d i))
                        w)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Rat.cast.{0} Real Real.instRatCast δ))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Rat.cast.{0} Real Real.instRatCast (@BalancedAssortments.FPTAS.revenue n d y)))))))) := by
  sorry

/-- L9: `BalancedAssortments.Knapsack.solve_relative_all_selections`. -/
theorem claim_030 :
  (∀ {δ maxProfit capacity : Rat} {groups : List.{0} (List.{0} BalancedAssortments.Knapsack.Item)}
  {s t : BalancedAssortments.Knapsack.State}
  (hδ : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) δ)
  (hm : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) maxProfit)
  (hn :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.length.{0} (List.{0} BalancedAssortments.Knapsack.Item) groups))
  (hs :
    @Eq.{1} (Option.{0} BalancedAssortments.Knapsack.State)
      (BalancedAssortments.Knapsack.solve
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) δ maxProfit)
          (@Nat.cast.{0} Rat Rat.instNatCast (@List.length.{0} (List.{0} BalancedAssortments.Knapsack.Item) groups)))
        capacity
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@List.length.{0} (List.{0} BalancedAssortments.Knapsack.Item) groups)
          (@Nat.ceil.{0} Rat Rat.semiring Rat.instPartialOrder
            (@FloorRing.toFloorSemiring.{0} Rat
              (@NormedRing.toRing.{0} Rat
                (@NormedCommRing.toNormedRing.{0} Rat (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField)))
              Rat.linearOrder Rat.instIsStrictOrderedRing Rat.instFloorRing)
            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
              (@Nat.cast.{0} Rat Rat.instNatCast (@List.length.{0} (List.{0} BalancedAssortments.Knapsack.Item) groups))
              δ)))
        groups)
      (@Option.some.{0} BalancedAssortments.Knapsack.State s))
  (ht :
    BalancedAssortments.Knapsack.Selection
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) δ maxProfit)
        (@Nat.cast.{0} Rat Rat.instNatCast (@List.length.{0} (List.{0} BalancedAssortments.Knapsack.Item) groups)))
      groups t)
  (hweights :
    ∀ (group : List.{0} BalancedAssortments.Knapsack.Item),
      @Membership.mem.{0, 0} (List.{0} BalancedAssortments.Knapsack.Item)
          (List.{0} (List.{0} BalancedAssortments.Knapsack.Item))
          (@List.instMembership.{0} (List.{0} BalancedAssortments.Knapsack.Item)) groups group →
        ∀ (item : BalancedAssortments.Knapsack.Item),
          @Membership.mem.{0, 0} BalancedAssortments.Knapsack.Item (List.{0} BalancedAssortments.Knapsack.Item)
              (@List.instMembership.{0} BalancedAssortments.Knapsack.Item) group item →
            @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (BalancedAssortments.Knapsack.Item.weight item))
  (hprofits :
    ∀ (group : List.{0} BalancedAssortments.Knapsack.Item),
      @Membership.mem.{0, 0} (List.{0} BalancedAssortments.Knapsack.Item)
          (List.{0} (List.{0} BalancedAssortments.Knapsack.Item))
          (@List.instMembership.{0} (List.{0} BalancedAssortments.Knapsack.Item)) groups group →
        ∀ (item : BalancedAssortments.Knapsack.Item),
          @Membership.mem.{0, 0} BalancedAssortments.Knapsack.Item (List.{0} BalancedAssortments.Knapsack.Item)
              (@List.instMembership.{0} BalancedAssortments.Knapsack.Item) group item →
            And
              (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                (BalancedAssortments.Knapsack.Item.profit item))
              (@LE.le.{0} Rat Rat.instLE (BalancedAssortments.Knapsack.Item.profit item) maxProfit))
  (hw : @LE.le.{0} Rat Rat.instLE (BalancedAssortments.Knapsack.State.weight t) capacity)
  (hmax : @LE.le.{0} Rat Rat.instLE maxProfit (BalancedAssortments.Knapsack.State.profit t)),
  @LE.le.{0} Rat Rat.instLE
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) δ)
      (BalancedAssortments.Knapsack.State.profit t))
    (BalancedAssortments.Knapsack.State.profit s)) := by
  sorry

/-- L9: `BalancedAssortments.KnapsackCostState.solve_decode`. -/
theorem claim_031 :
  (∀ {cap : BalancedAssortments.KnapsackCostRational.Fraction} {bound : Nat}
  {groups : List.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item)} {θ : Rat}
  (hc : BalancedAssortments.KnapsackCostRational.Fraction.Valid cap)
  (hi :
    ∀ (g : List.{0} BalancedAssortments.KnapsackCostState.Item),
      @Membership.mem.{0, 0} (List.{0} BalancedAssortments.KnapsackCostState.Item)
          (List.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item))
          (@List.instMembership.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item)) groups g →
        ∀ (i : BalancedAssortments.KnapsackCostState.Item),
          @Membership.mem.{0, 0} BalancedAssortments.KnapsackCostState.Item
              (List.{0} BalancedAssortments.KnapsackCostState.Item)
              (@List.instMembership.{0} BalancedAssortments.KnapsackCostState.Item) g i →
            And (BalancedAssortments.KnapsackCostState.Item.Valid i)
              (@Eq.{1} Nat
                (BalancedAssortments.ComplexityTimeBinary.value (BalancedAssortments.KnapsackCostState.Item.scaled i))
                (BalancedAssortments.Knapsack.scaledProfit θ (BalancedAssortments.KnapsackCostState.Item.decode i)))),
  @Eq.{1} (Option.{0} BalancedAssortments.Knapsack.State)
    (@Option.map.{0, 0} BalancedAssortments.KnapsackCostState.State BalancedAssortments.Knapsack.State
      BalancedAssortments.KnapsackCostState.State.decode
      (@Prod.fst.{0, 0} (Option.{0} BalancedAssortments.KnapsackCostState.State) Nat
        (BalancedAssortments.KnapsackCostState.solve cap bound groups)))
    (BalancedAssortments.Knapsack.solve θ (BalancedAssortments.KnapsackCostRational.Fraction.decode cap) bound
      (@List.map.{0, 0} (List.{0} BalancedAssortments.KnapsackCostState.Item)
        (List.{0} BalancedAssortments.Knapsack.Item)
        (@List.map.{0, 0} BalancedAssortments.KnapsackCostState.Item BalancedAssortments.Knapsack.Item
          BalancedAssortments.KnapsackCostState.Item.decode)
        groups))) := by
  sorry

/-- L9: `BalancedAssortments.KnapsackCostState.solve_cost`. -/
theorem claim_032 :
  (∀ {cap : BalancedAssortments.KnapsackCostRational.Fraction} {bound : Nat}
  {groups : List.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item)} {b M : Nat}
  (hc : BalancedAssortments.KnapsackCostRational.Fraction.Width cap b)
  (hi :
    ∀ (g : List.{0} BalancedAssortments.KnapsackCostState.Item),
      @Membership.mem.{0, 0} (List.{0} BalancedAssortments.KnapsackCostState.Item)
          (List.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item))
          (@List.instMembership.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item)) groups g →
        And (@LE.le.{0} Nat instLENat (@List.length.{0} BalancedAssortments.KnapsackCostState.Item g) M)
          (∀ (i : BalancedAssortments.KnapsackCostState.Item),
            @Membership.mem.{0, 0} BalancedAssortments.KnapsackCostState.Item
                (List.{0} BalancedAssortments.KnapsackCostState.Item)
                (@List.instMembership.{0} BalancedAssortments.KnapsackCostState.Item) g i →
              BalancedAssortments.KnapsackCostState.Item.Width i b)),
  have W : Nat :=
    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@List.length.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item) groups)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      b;
  @LE.le.{0} Nat instLENat
    (@Prod.snd.{0, 0} (Option.{0} BalancedAssortments.KnapsackCostState.State) Nat
      (BalancedAssortments.KnapsackCostState.solve cap bound groups))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@List.length.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item) groups)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (BalancedAssortments.KnapsackCostState.rowCost
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                M
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                W (@List.length.{0} (List.{0} BalancedAssortments.KnapsackCostState.Item) groups))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) W)
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))) := by
  sorry

/-- Model: `BalancedAssortments.Sales.sales_total_probability`. -/
theorem claim_033.{u_1, u_2} :
  (∀ {I : Type u_1} {A : Type u_2} [inst : Fintype.{u_1} I] [inst_1 : DecidableEq.{u_1 + 1} I] [inst_2 : Fintype.{u_2} A]
  (v : I → Real)
  (hv :
    ∀ (i : I),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  (S : A → Finset.{u_1} I) {q : A → Real} (hq : @BalancedAssortments.Sales.Distribution.{u_2} A inst_2 q),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@BalancedAssortments.Sales.outside.{u_1, u_2} I A inst_2 v S q)
      (@Finset.sum.{u_1, 0} I Real Real.instAddCommMonoid (@Finset.univ.{u_1} I inst) fun (i : I) =>
        @BalancedAssortments.Sales.sales.{u_1, u_2} I A inst_1 inst_2 v S q i))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := by
  sorry

/-- Model: `BalancedAssortments.Sales.outside_pos`. -/
theorem claim_034.{u_1, u_2} :
  (∀ {I : Type u_1} {A : Type u_2} [Fintype.{u_1} I] [DecidableEq.{u_1 + 1} I] [inst : Fintype.{u_2} A] (v : I → Real)
  (hv :
    ∀ (i : I),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  (S : A → Finset.{u_1} I) {q : A → Real} (hq : @BalancedAssortments.Sales.Distribution.{u_2} A inst q),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@BalancedAssortments.Sales.outside.{u_1, u_2} I A inst v S q)) := by
  sorry

/-- Model: `BalancedAssortments.Sales.active_catalog_iff`. -/
theorem claim_035.{u_1, u_2} :
  (∀ {I : Type u_1} {A : Type u_2} [Fintype.{u_1} I] [inst : Fintype.{u_2} A] [inst_1 : DecidableEq.{u_1 + 1} I]
  (v : I → Real)
  (hv :
    ∀ (i : I),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v i))
  (S : A → Finset.{u_1} I) (q : A → Real)
  (hq :
    ∀ (a : A),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (q a))
  (i : I),
  Iff
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@BalancedAssortments.Sales.sales.{u_1, u_2} I A inst_1 inst v S q i))
    (@Exists.{u_2 + 1} A fun (a : A) =>
      And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (q a))
        (@Membership.mem.{u_1, u_1} I (Finset.{u_1} I) (@Finset.instMembership.{u_1} I) (S a) i))) := by
  sorry

/-- Model: `BalancedAssortments.Sales.balanced_iff_max_coordinate`. -/
theorem claim_036.{u_1} :
  (∀ {I : Type u_1} [Fintype.{u_1} I] [DecidableEq.{u_1 + 1} I] (α : Real)
  (hα : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α)
  (x : I → Real) (k : I) (hk : ∀ (j : I), @LE.le.{0} Real Real.instLE (x j) (x k)),
  Iff (@BalancedAssortments.Sales.Balanced.{u_1} I α x)
    (∀ (i : I),
      Or (@Eq.{1} Real (x i) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@LE.le.{0} Real Real.instLE (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) α (x k))
          (x i)))) := by
  sorry

end BalancedAssortmentsAudit
