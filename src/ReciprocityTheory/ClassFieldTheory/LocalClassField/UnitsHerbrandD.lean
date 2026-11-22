module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandC

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
