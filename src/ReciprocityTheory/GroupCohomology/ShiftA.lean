import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.Shapiro

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section Disc

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def subRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := S
  ccs := ⟨fun _ => continuous_of_discreteTopology⟩
  rho := B.rho.subrepresentation S hS
  cont := contAction_of_disc _ fun v => (orbit_cont B v.1).subtype_mk _

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (subRep B S hS).V := inferInstanceAs (DiscreteTopology S)

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (quotRep B S hS).V := disc_quot S

end Disc

section ShiftC

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]

instance disc_resBot : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V :=
  inferInstanceAs (DiscreteTopology M.V)

instance disc_shC : DiscreteTopology (shC M).V := by
  have := disc_CM (X := G) (Y := (M.resSub (⊥ : Subgroup G)).V)
  exact inferInstanceAs (DiscreteTopology (coindSub (⊥ : Subgroup G) (M.resSub ⊥)))

end ShiftC

end KernelCokernelKilling

end

end ReciprocityTheory.Coh
