import BalancedAssortments.ComplexityTimeReduction
import BalancedAssortments.EncodingTime

/-! The fully serialized bit-list transducer, including input parsing and output
serialization. Polynomial running cost is proved in the explicit bit/list model. -/
namespace BalancedAssortments.ComplexityTimeEndToEnd
open ComplexityEncoding ComplexityTimeReduction

/-- Parse the source, then run the concrete bitwise reduction. Malformed source
strings deterministically produce an empty output. -/
def binaryReduction (input : List Bool) : List Bool × ℕ :=
  let p := EncodingTime.parse input
  match p.1 with
  | some (B :: items) =>
      let r := runReduction B items
      (r.1,p.2+r.2+4)
  | _ => ([],p.2+4)

/-- End-to-end exact bytes and polynomial binary-operation bound. All integer
arithmetic on substantive data is implemented by Boolean/list algorithms. -/
theorem binaryReduction_correct_and_cost (B : ℕ) (items : List ℕ) :
    (binaryReduction (encodeFields (B::items))).1 = completeReductionBits B items ∧
    (binaryReduction (encodeFields (B::items))).2 ≤
      1025*((encodeFields (B::items)).length+1)^2 := by
  have hp := EncodingTime.parse_encoded (B::items)
  have hr := runReduction_binary_polynomial B items
  simp only [binaryReduction, hp.1, List.map_cons]
  refine ⟨hr.1, ?_⟩
  have hpc := hp.2
  have hrc := hr.2
  unfold inputLength at hrc
  have hs : 1 ≤ ((encodeFields (B::items)).length+1)^2 := by
    have hpos : 0 < ((encodeFields (B::items)).length+1)^2 := by positivity
    exact hpos
  nlinarith

end BalancedAssortments.ComplexityTimeEndToEnd
