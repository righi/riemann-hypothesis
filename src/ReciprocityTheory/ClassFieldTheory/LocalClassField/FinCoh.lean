import Mathlib
import ReciprocityTheory.GroupCohomology.IsLowExists
import ReciprocityTheory.GroupCohomology.LowNat
import ReciprocityTheory.NeutralLocalFields.Duality

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

theorem sub_toLinearMap (M : TRep R C) (g : C) :
    (Rep.applyAsHom (Rep.of M.rho) g - 𝟙 (Rep.of M.rho)).hom.toLinearMap = M.rho g - LinearMap.id := rfl

end Cyclic

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
