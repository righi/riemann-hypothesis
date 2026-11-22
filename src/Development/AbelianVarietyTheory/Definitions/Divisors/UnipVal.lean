module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped Topology Classical

namespace GlobalTheory.KSp

open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitUnitary

section Abstract

variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

structure IsPair (e : X → X → ℂ) : Prop where
  add : ∀ x x' y, e (x + x') y = e x y * e x' y
  symm : ∀ x y, e x y = e y x
  norm : ∀ x y, ‖e x y‖ = 1
  lc : IsLocallyConstant fun p : X × X => e p.1 p.2
  small : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ K, e x y = 1) → y ∈ U
  big : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ U, e x y = 1) → y ∈ K

variable [MeasurableSpace X]

end Abstract

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

abbrev mat (g : UG c (stdJ ν E)) : Matrix (ν ⊕ ν) (ν ⊕ ν) E := ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def sc (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : E) : ℂ :=
  if h : z = 0 then 0 else (χ (Units.mk0 z h) : ℂ) *
    ((nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z h)) ^ ((m : ℝ) / 2) : ℝ) : ℂ)

end Local

end GlobalTheory.KSp

end
