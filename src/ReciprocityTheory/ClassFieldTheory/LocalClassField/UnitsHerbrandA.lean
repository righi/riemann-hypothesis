module

public import Mathlib

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

section approx

variable {U : Type*} [CommGroup U]

end approx

variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]

structure Filt (I : ℕ → AddSubgroup R) (e : R →+ R) : Prop where
  anti : ∀ n, I (n + 1) ≤ I n
  mul : ∀ n x y, x ∈ I n → y ∈ I 0 → x * y ∈ I (n + 1)
  smul : ∀ n (g : G) x, x ∈ I n → g • x ∈ I n
  comp : ∀ x : ℕ → R, (∀ k, x k ∈ I k) → ∃ s, ∀ n, s - ∑ k ∈ range n, x k ∈ I n
  sep : ∀ x, (∀ n, x ∈ I n) → x = 0
  inv : ∀ n x, x ∈ I n → (1 + x)⁻¹ - 1 ∈ I n
  e_mem : ∀ n x, x ∈ I n → e x ∈ I n
  e_sum : ∀ x, ∑ g : G, g • e (g⁻¹ • x) = x

namespace Filt

variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem le_zero (n : ℕ) : I n ≤ I 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (h.anti n).trans ih

theorem mul_unit {n : ℕ} {x u : R} (hx : x ∈ I n) (hu : u - 1 ∈ I 0) : x * u ∈ I n := by
  have : x * u = x * (u - 1) + x := by ring
  rw [this]
  exact (I n).add_mem (h.anti n (h.mul n _ _ hx hu)) hx

def V (n : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I n}
  one_mem' := by simp
  mul_mem' := fun {u v} hu hv => by
    have hu' : (u : R) - 1 ∈ I n := hu
    have hv' : (v : R) - 1 ∈ I n := hv
    show ((u * v : Rˣ) : R) - 1 ∈ I n
    have : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * v + ((v : R) - 1) := by
      rw [Units.val_mul]; ring
    rw [this]
    exact (I n).add_mem (h.mul_unit hu' (h.le_zero n hv')) hv'
  inv_mem' := fun {u} hu => by
    have hu' : (u : R) - 1 ∈ I n := hu
    show ((u⁻¹ : Rˣ) : R) - 1 ∈ I n
    have := h.inv n _ hu'
    rwa [add_sub_cancel, ← Units.val_inv_eq_inv_val] at this

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
