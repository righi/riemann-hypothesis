import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

variable {K L}

theorem mem_ball {t : ℝ} {ht : 0 ≤ t} {x : L} : x ∈ ball K L t ht ↔ ‖Phi K L x‖ ≤ t := Iff.rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
