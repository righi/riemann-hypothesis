module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandA

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]

variable (G) in
namespace Filt

variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
