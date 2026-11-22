module

public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.ConnNatHolds
public import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
public import ReciprocityTheory.GroupCohomology.Shapiro

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section Disc

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem contAction_of_disc {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [DiscreteTopology V] (rho : Representation R G V) (h : ∀ v, Continuous fun g => rho g v) :
    ContAction rho :=
  continuous_prod_of_discrete_right.2 h

theorem orbit_cont (B : TRep R G) (v : B.V) : Continuous fun g => B.rho g v :=
  B.cont.comp (f := fun g : G => (g, v)) (continuous_id.prodMk continuous_const)

theorem disc_quot {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [DiscreteTopology V]
    (S : Submodule R V) : DiscreteTopology (V ⧸ S) :=
  discreteTopology_iff_forall_isOpen.2 fun _ =>
    (Submodule.isQuotientMap_mkQ S).isOpen_preimage.1 (isOpen_discrete _)

def quotRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := B.V ⧸ S
  ccs := ⟨fun _ => by have := disc_quot S; exact continuous_of_discreteTopology⟩
  rho := B.rho.quotient S hS
  cont := by
    have := disc_quot S
    refine contAction_of_disc _ fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (continuous_of_discreteTopology (f := S.mkQ)).comp (orbit_cont B v)

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (quotRep B S hS).V := disc_quot S

end Disc

section Triv

variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]

end Triv

section ShiftSec

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G]

end ShiftSec

section ShiftC

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]

end ShiftC

end KernelCokernelKilling

end

end ReciprocityTheory.Coh
