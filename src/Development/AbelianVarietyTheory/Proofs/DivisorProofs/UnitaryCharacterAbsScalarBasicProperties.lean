import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.ScBasic

end GlobalTheory.KSp.ScBasic
namespace GlobalTheory.KSp

open MeasureTheory Matrix in
private theorem sc_units_eq_mul_nabs_norm_rpow {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : Eˣ) :
    _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := by
  simp [_root_.GlobalTheory.KSp.sc, z.ne_zero]

open MeasureTheory Matrix in
private theorem rpow_natCast_div_two_sq {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x ^ ((m : ℝ) / 2)) ^ 2 = x ^ m := by
  rw [← Real.rpow_natCast (x ^ ((m : ℝ) / 2)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x m]
  congr 1
  push_cast
  ring

open MeasureTheory Matrix in
private theorem sc_zero' {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) : _root_.GlobalTheory.KSp.sc F χ m 0 = 0 := by
  simp [_root_.GlobalTheory.KSp.sc]

end GlobalTheory.KSp
