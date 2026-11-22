import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

omit [Algebra R R'] in
@[simp] lemma consZero_zero (n : ℕ) (w : Fin n → R') : consZero n w 0 = 0 := rfl

omit [Algebra R R'] in
@[simp] lemma consZero_succ (n : ℕ) (w : Fin n → R') (j : Fin n) : consZero n w j.succ = w j := rfl

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory.StableLatticeDescent

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory

end GlobalTheory
