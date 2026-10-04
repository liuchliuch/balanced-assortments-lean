import BalancedAssortments.Knapsack
import BalancedAssortments.Grids

/-! Small kernel-checked executable regression examples. -/
namespace BalancedAssortments.KnapsackExamples
open Knapsack

def zeroItem : Item := ⟨0, 0, 0⟩
def firstItem : Item := ⟨1, 1/2, 4⟩
def secondItem : Item := ⟨1, 1/2, 3⟩

theorem geometric_grid_example : Grids.geometricGrid 1 1 8 3 = [1,2,4,8] := by decide +kernel

theorem exact_capacity_example :
    solve 1 1 7 [[zeroItem, firstItem], [zeroItem, secondItem]] =
      some ⟨1, 7, 7, [1,1]⟩ := by decide +kernel

theorem capacity_exclusion_example :
    solve 1 (1/2) 7 [[zeroItem, firstItem], [zeroItem, secondItem]] =
      some ⟨1/2, 4, 4, [1,0]⟩ := by decide +kernel

end BalancedAssortments.KnapsackExamples
