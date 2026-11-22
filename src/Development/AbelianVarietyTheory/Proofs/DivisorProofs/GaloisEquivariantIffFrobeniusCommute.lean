import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusEndomorphism
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] [Fintype K]

local notation "Fr" K => FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)

variable (l : ℕ) [Fact l.Prime]

abbrev tv (A : AbVar K) : Tl l A →ₗ[ℤ_[l]] Vl l A := TensorProduct.mk ℤ_[l] ℚ_[l] (Tl l A) 1

instance isLocalizedModule_tv (A : AbVar K) : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (tv l A) := by
  rw [isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l]]
  exact TensorProduct.isBaseChange _ _ _

theorem galV_tv (A : AbVar K) (σ : Gal K) (t : Tl l A) : galV l A σ (tv l A t) = tv l A (galT l A σ t) := rfl

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

end GlobalTheory.AV.AbVar
