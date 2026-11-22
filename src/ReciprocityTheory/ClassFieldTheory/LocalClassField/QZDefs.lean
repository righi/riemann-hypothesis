module

public import Mathlib
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.ContinuousContractNth

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

def trivRep (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] : TRep ℤ G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  { V := A
    rho := 1
    cont := continuous_snd }

scoped instance (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] :
    DiscreteTopology (trivRep G A).V := ⟨rfl⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
