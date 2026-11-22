import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.PartialProdCoe

namespace ReciprocityTheory.Coh

namespace QuadraticConjugation

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjHom (U : Subgroup G) [U.Normal] (s : G) : U →* U where
  toFun g := ⟨s⁻¹ * g * s, by simpa using ‹U.Normal›.conj_mem g g.2 s⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] theorem conjHom_coe (U : Subgroup G) [U.Normal] (s : G) (g : U) :
    ((conjHom U s g : U) : G) = s⁻¹ * g * s := rfl

end

end QuadraticConjugation

end ReciprocityTheory.Coh
