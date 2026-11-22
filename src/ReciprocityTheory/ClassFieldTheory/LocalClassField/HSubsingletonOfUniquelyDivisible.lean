module

public import Mathlib
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.ImportsAlt
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.MemZmultiplesOfAddOrderOf

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
