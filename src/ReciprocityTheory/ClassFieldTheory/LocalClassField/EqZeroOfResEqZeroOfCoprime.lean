module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.SubsingletonHOfSubsingleton

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open ReciprocityTheory.Coh Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
