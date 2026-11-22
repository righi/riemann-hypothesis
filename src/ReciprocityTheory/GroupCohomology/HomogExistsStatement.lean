module

public import ReciprocityTheory.GroupCohomology.ContinuousContractNth

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def hcoch (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ) :
    Submodule R ((Fin (n + 1) → X) → M.V) where
  carrier := {F | Continuous F ∧ ∀ (g : G) x, F (fun i => g • x i) = M.rho g (F x)}
  zero_mem' := ⟨continuous_const, fun g x => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g x => by simp [ha.2, hb.2]⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun g x => by simp [ha.2]⟩

def hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) (x : Fin (n + 2) → X) : V :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F fun j => x (i.succAbove j)

def IsHomog (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (A : Cx R)
    (e : ∀ n, A.X n ≃ₗ[R] hcoch M X n) : Prop :=
  ∀ n a, (e (n + 1) (A.d n a)).1 = hd n (e n a).1

def HomogExistsStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X],
  ∃ A e, IsHomog M X A e

end

end ReciprocityTheory.Coh
