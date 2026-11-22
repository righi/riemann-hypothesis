import ReciprocityTheory.GroupCohomology.TransgressionStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.LowNat
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.PartialProdCoe

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal LowDeg

universe u

private theorem exact_of_linearEquiv_conj {R X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂] [AddCommGroup Y₃] [Module R Y₃]
    {f : X₁ →ₗ[R] X₂} {g : X₂ →ₗ[R] X₃} {f' : Y₁ →ₗ[R] Y₂} {g' : Y₂ →ₗ[R] Y₃}
    (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂) (e₃ : X₃ ≃ₗ[R] Y₃)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (hg : ∀ x, e₃ (g x) = g' (e₂ x))
    (h : Function.Exact f g) : Function.Exact f' g' := by
  intro y
  obtain ⟨x, rfl⟩ := e₂.surjective y
  rw [← hg, LinearEquiv.map_eq_zero_iff, h x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e₁ z, (hf z).symm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := e₁.surjective w
    refine ⟨z, e₂.injective ?_⟩
    rw [hf]
    exact hw

private theorem injective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Injective f) : Function.Injective f' := by
  intro a b hab
  obtain ⟨x, rfl⟩ := e₁.surjective a
  obtain ⟨z, rfl⟩ := e₁.surjective b
  rw [← hf, ← hf] at hab
  rw [h (e₂.injective hab)]

private theorem surjective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Surjective f) : Function.Surjective f' := by
  intro y
  obtain ⟨x, hx⟩ := h (e₂.symm y)
  refine ⟨e₁ x, ?_⟩
  rw [← hf, hx, LinearEquiv.apply_symm_apply]

end ReciprocityTheory.Coh
