module

public import Mathlib
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel

structure Model (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (p : ℕ) [Fact p.Prime] where
  K' : IntermediateField ℚ_[p] (PadicAlgCl p)
  fin : FiniteDimensional ℚ_[p] K'
  e : K ≃+* K'
  E : AlgebraicClosure K ≃+* PadicAlgCl p
  comm : ∀ x, E (algebraMap K (AlgebraicClosure K) x) = (e x : PadicAlgCl p)
  homeo : IsHomeomorph e
  int : ∀ x, x ∈ 𝒪[K] ↔ ‖(e x : PadicAlgCl p)‖ ≤ 1

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime]

def Model.Corr (m : Model K p) (L : IntermediateField K (AlgebraicClosure K))
    (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop := ∀ x, m.E x ∈ L' ↔ x ∈ L

end ReciprocityTheory.DiscreteGroups.LocalClassField
