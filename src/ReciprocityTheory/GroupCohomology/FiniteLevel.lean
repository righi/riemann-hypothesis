module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.ResNormalHolds
public import ReciprocityTheory.GroupCohomology.InfRes

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

namespace FiniteLevelCohomology

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem stab_mem_nhds (M : TRep R G) [DiscreteTopology M.V] (m : M.V) :
    {a : G | M.rho a m = m} ∈ 𝓝 (1 : G) := by
  have hc : Continuous fun a : G => M.rho a m :=
    M.cont.comp (Continuous.prodMk continuous_id continuous_const)
  exact (hc.isOpen_preimage {m} (isOpen_discrete _)).mem_nhds (by simp)

end FiniteLevelCohomology

namespace FiniteLevelCohomology

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end FiniteLevelCohomology

end ReciprocityTheory.Coh
