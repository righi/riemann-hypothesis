module

public import ReciprocityTheory.GroupCohomology.ModelComparisonDegreeZeroBijective

@[expose] public section

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def tr (M : TRep R G) (f : G × G → M.V) (s : G) : ℕ → M.V
  | 0 => f (1, 1)
  | j + 1 => tr M f s j - f (s ^ j, s)

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end ProcyclicCohomology

end ReciprocityTheory.Coh
