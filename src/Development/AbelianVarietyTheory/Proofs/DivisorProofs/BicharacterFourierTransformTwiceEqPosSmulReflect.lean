module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

noncomputable section
namespace GlobalTheory.KSp.FourInv

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}

variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]

end GlobalTheory.KSp.FourInv

namespace GlobalTheory.KSp


end GlobalTheory.KSp

end
