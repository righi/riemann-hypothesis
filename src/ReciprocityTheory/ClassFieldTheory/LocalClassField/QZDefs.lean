import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

scoped instance (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] :
    DiscreteTopology (trivRep G A).V := ⟨rfl⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
