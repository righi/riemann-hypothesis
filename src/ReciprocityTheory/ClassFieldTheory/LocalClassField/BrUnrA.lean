module

public import Mathlib
public import ReciprocityTheory.GroupCohomology.ImportsAlt
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.HSubsingletonOfUniquelyDivisible
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
