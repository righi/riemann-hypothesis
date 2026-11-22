import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw

theorem sec_eq_zero_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = 0) : s = 0 := by
  apply GlobalTheory.LB.f_injective
  funext i
  refine finSec_eq_zero_of_cover V hc (s.f i) fun a => ?_
  have h₁ : rs X (inf_le_left : L.U i ⊓ V a ≤ L.U i) (s.f i) =
      rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)) (L.g i (c a)).val *
        rs X (inf_le_right : L.U i ⊓ V a ≤ V a) (rs X (hV a) (s.f (c a))) := by
    have h := congrArg (rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)))
      (s.compat i (c a))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  rw [h₁, h a, map_zero, mul_zero]

section PerfSec

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
  {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) {g : R →+* R'} {π : X' ⟶ X}
  {f' : X' ⟶ Spec (CommRingCat.of R')}
  (E : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π))

theorem Perf.iSup_preimage : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, Q.cover]
  exact top_unique fun _ _ => trivial

end PerfSec

end GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

end GlobalTheory.AbLaw
