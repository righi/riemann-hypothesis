import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section Push

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)

theorem shpPush_apply (n : ℕ) (F : hcoch C G n) (x) : (shpPush ev hφ n F).1 x = ev.u (F.1 x) := rfl

variable (j : C.V → C(G, M.V)) (hj : Topology.IsEmbedding j) (hjc : ∀ c g, j c g = ev.u (C.rho g c))
  (hr : ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j)

end Push

section Coind

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (M : TRep R U)

variable {U M}

@[simp] theorem coindTr_apply (g : G) (f : coindSub U M) (h : G) : (coindTr g f).1 h = f.1 (h * g) := rfl

variable (U M)

instance : ContinuousConstSMul R (coindSub U M) :=
  ⟨fun c => ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩

variable [LocallyCompactSpace G]

end Coind

end

end ReciprocityTheory.Coh
