import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem invMap_φ {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (σ : G') :
    (invMap Q N N' hN).φ (QuotientGroup.mk σ) = QuotientGroup.mk (Q.φ σ) := rfl

theorem invMap_u {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (x : (InflationRestrictionInvariants.invQ M N).V) :
    ((invMap Q N N' hN).u x).1 = Q.u x.1 := rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
