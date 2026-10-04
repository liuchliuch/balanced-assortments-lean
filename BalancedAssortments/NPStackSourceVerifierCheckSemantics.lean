import BalancedAssortments.NPStackSourceVerifierBalanceData

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma zle_value_congr (x y a b : ZBits) (hx : zvalue x=zvalue a) (hy : zvalue y=zvalue b) :
    (zle x y).1=(zle a b).1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [zle_correct,hx,hy]

lemma balance_check_congr (αn αd m m' : ZBits) (x : WitnessRecord) (hm : zvalue m=zvalue m') :
    checkBalance αn αd m x=checkBalance αn αd m' x := by
  cases h : x.active <;> simp only [checkBalance,h,Bool.false_eq_true,if_false,if_true]
  exact zle_value_congr _ _ _ _ (by simp [zmul_value,hm]) rfl

lemma final_check_represented (s : Registers) (a : StreamState)
    (h : Represents s a) (H : ComplexityTimeFractions.Fraction) (K : List Bool)
    (hK : s .capacity=(K,[])) (hH : s .target=H.num) (hHd : s .targetDen=(H.den,[])) :
    ((eval VerifierCommands.rankCommand s).1 && (eval VerifierCommands.revenueCommand s).1)=
      checkFinal H H K (s .q) a := by
  rcases h with ⟨hr,hv,ht,hm⟩
  have hrd:=congrArg Prod.fst hr;have hrn:=congrArg Prod.snd hr
  have hvd:=congrArg Prod.fst hv;have hvn:=congrArg Prod.snd hv
  simp only [registerState] at hrd hrn hvd hvn ht
  simp only [VerifierCommands.rankCommand_accepts,VerifierCommands.revenueCommand_accepts,
    hK,hH,hHd,hrd,hrn,hvd,hvn,ht,checkFinal]

end BalancedAssortments.NPStack.SourceVerifier
