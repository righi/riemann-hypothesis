import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]

theorem act_val (g : G) (u : Rˣ) : ((act g u : Rˣ) : R) = g • (u : R) := rfl

namespace Filt

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
