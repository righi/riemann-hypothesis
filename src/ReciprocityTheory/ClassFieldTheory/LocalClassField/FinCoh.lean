module

public import Mathlib
public import ReciprocityTheory.GroupCohomology.IsLowExists
public import ReciprocityTheory.GroupCohomology.LowNat
public import ReciprocityTheory.NeutralLocalFields.Duality

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open ReciprocityTheory.Coh CategoryTheory

noncomputable section

universe u

variable {R : Type u} [CommRing R]

section Discrete

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

def pairRepHom {M : TRep R G} {M' : TRep R G'} (P : Pair M M') :
    Rep.res P.φ (Rep.of M.rho) ⟶ Rep.of M'.rho :=
  Rep.ofHom ⟨P.u, fun g => LinearMap.ext fun m => P.equiv g m⟩

open groupCohomology

variable [DiscreteTopology G] [DiscreteTopology G']

end Discrete

section Cyclic

variable {C : Type u} [CommGroup C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C]
  [DiscreteTopology C]

end Cyclic

section Low

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

end Low

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
