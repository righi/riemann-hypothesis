module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
public import ReciprocityTheory.GroupCohomology.HomogExistsStatement
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.HomogIso
public import ReciprocityTheory.GroupCohomology.PrismOpZeroEval

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section QI

variable {R : Type u} [CommRing R] {A B : Cx R}

end QI

section Push

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)

variable (j : C.V → C(G, M.V)) (hj : Topology.IsEmbedding j) (hjc : ∀ c g, j c g = ev.u (C.rho g c))
  (hr : ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j)

end Push

section Coind

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (M : TRep R U)

def coindSub : Submodule R C(G, M.V) where
  carrier := {f | ∀ (x : U) g, f (x * g) = M.rho x (f g)}
  zero_mem' := fun x g => by simp
  add_mem' := fun {a b} ha hb x g => by simp [ha x g, hb x g]
  smul_mem' c a ha x g := by simp [ha x g]

variable {U M}

variable (U M)

instance : ContinuousConstSMul R (coindSub U M) :=
  ⟨fun c => ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩

variable [LocallyCompactSpace G]

end Coind

end

end ReciprocityTheory.Coh
