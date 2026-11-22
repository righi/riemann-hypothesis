import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinChange

end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj coord iSup_nonzeroLocus_coord toProj_coord)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

instance isIso_linAut (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) : IsIso (linAut a ha) := by
  have hb : IsUnit a⁻¹.det := Matrix.isUnit_nonsing_inv_det a ha
  refine ⟨⟨linAut a⁻¹ hb, ?_, ?_⟩⟩
  · rw [linAut_comp a a⁻¹ ha hb (by rw [Matrix.nonsing_inv_mul a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.nonsing_inv_mul a ha]
    exact linAut_one _
  · rw [linAut_comp a⁻¹ a hb ha (by rw [Matrix.mul_nonsing_inv a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.mul_nonsing_inv a ha]
    exact linAut_one _

end GlobalTheory.LinChange

