import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary

noncomputable section

open MeasureTheory Matrix
open scoped Topology Classical

namespace GlobalTheory.KSp

open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitUnitary

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem weyl_val : ((weyl c ν : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = stdJ ν E := rfl

theorem unip_val (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    ((unip c b hb : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = fromBlocks 1 b 0 1 := rfl

theorem mem_sieg {g : UG c (stdJ ν E)} : g ∈ sieg c ν ↔ (mat c g).toBlocks₂₁ = 0 := by
  exact Iff.rfl

end Group

end GlobalTheory.KSp

end
