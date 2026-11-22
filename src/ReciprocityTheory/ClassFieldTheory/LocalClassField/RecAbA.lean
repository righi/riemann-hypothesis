import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

noncomputable section

scoped instance hasEnoughRootsOfUnity_QZ (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (Multiplicative QZ) n where
  prim := ⟨Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n)),
    { pow_eq_one := by
        rw [← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]; rfl
      dvd_of_pow_eq_one := fun l hl => by
        rw [← ofAdd_nsmul] at hl
        exact (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) l).1 (Multiplicative.ofAdd.injective hl) }⟩
  cyc := by
    have h0 : (toUnits (Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ))) ∈
        rootsOfUnity n (Multiplicative QZ) := by
      rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]
      exact map_one _
    refine ⟨⟨⟨_, h0⟩, fun x => ?_⟩⟩
    have hx : n • Multiplicative.toAdd (x.1 : Multiplicative QZ) = 0 := by
      have := x.2
      rw [mem_rootsOfUnity] at this
      have h2 := congrArg (fun u : (Multiplicative QZ)ˣ => Multiplicative.toAdd (u : Multiplicative QZ)) this
      simpa using h2
    obtain ⟨k, hk⟩ := qz_exists_zsmul n (NeZero.ne n) _ hx
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply Multiplicative.toAdd.injective
    rw [hk]
    simp

section fin

variable (A : Type) [AddCommGroup A] [Finite A]

theorem homEquivUnits_apply (χ : A →+ QZ) (a : A) :
    Multiplicative.toAdd ((homEquivUnits A χ (Multiplicative.ofAdd a) : (Multiplicative QZ)ˣ) : Multiplicative QZ) = χ a := rfl

scoped instance : NeZero (Monoid.exponent (Multiplicative A)) := ⟨Monoid.exponent_ne_zero_of_finite⟩

scoped instance finite_hom_QZ : Finite (A →+ QZ) :=
  Nat.finite_of_card_ne_zero (by rw [card_hom_QZ]; exact Nat.card_pos.ne')

variable {A}

end fin

section top

variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))

theorem pullChar_apply (ψ : A →+ QZ) (g : G) : (pullChar π hc ψ).1 (Additive.ofMul g) = ψ (π (Additive.ofMul g)) := rfl

variable {π}

include hc

end top

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
