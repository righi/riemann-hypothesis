module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section Defs
variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'}

def Pair.h0 (P : Pair M M') : H0 M.rho →ₗ[R] H0 M'.rho :=
  P.u.restrict fun m hm g => by rw [← P.equiv, hm (P.φ g)]

def Pair.h1 (P : Pair M M') : H1 M.rho →ₗ[R] H1 M'.rho :=
  pairH1DecompositionMap M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv

def Pair.h2 (P : Pair M M') : H2 M.rho →ₗ[R] H2 M'.rho :=
  compatiblePairH2 M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv

def IsLow (M : TRep R G) (e₀ : M.H 0 ≃ₗ[R] H0 M.rho) (e₁ : M.H 1 ≃ₗ[R] H1 M.rho)
    (e₂ : M.H 2 ≃ₗ[R] H2 M.rho) : Prop :=
  (∀ x hx, (e₀ (M.coch.cls 0 x hx) : M.V) = x.1 ![]) ∧
  (∀ x hx, ∃ hz : (fun g => x.1 ![g]) ∈ Z1 M.rho, e₁ (M.coch.cls 1 x hx) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
  ∀ x hx, ∃ hz : (fun g : G × G => x.1 ![g.1, g.2]) ∈ Z2 M.rho,
    e₂ (M.coch.cls 2 x hx) = Submodule.Quotient.mk ⟨_, hz⟩

def Cx.FinGen (A : Cx R) (N : ℕ) : Prop :=
  (∀ n, Module.Finite R (A.H n)) ∧ ∀ n, N < n → Subsingleton (A.H n)

def Cx.chiRk (A : Cx R) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1) ^ n * (Module.finrank R (A.H n) : ℤ)
end Defs

def LowNatStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  (M : TRep R G) (M' : TRep R G') (P : Pair M M') e₀ e₁ e₂ e₀' e₁' e₂', IsLow M e₀ e₁ e₂ → IsLow M' e₀' e₁' e₂' →
  (∀ x, e₀' (P.hom.H 0 x) = P.h0 (e₀ x)) ∧ (∀ x, e₁' (P.hom.H 1 x) = P.h1 (e₁ x)) ∧
  ∀ x, e₂' (P.hom.H 2 x) = P.h2 (e₂ x)

def LowResStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G),
  (∀ (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P →
    Injective P.h1 ∧ Exact P.h1 (resH1 M.rho N.subtype continuous_subtype_val)) ∧
  ∀ (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
    (∀ x, resH1 M.rho U.subtype continuous_subtype_val x = 0 → U.index • x = 0) ∧
    ∀ x, resH2 M.rho U.subtype continuous_subtype_val x = 0 → U.index • x = 0

def TransgressionStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → ∀ I : Submodule R ((M.resSub N).H 1),
  (∀ x, x ∈ I ↔ ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H 1 x = x) →
  ∃ tg : I →ₗ[R] Q.H 2,
    (∀ (y : M.coch.X 1) (z : Q.coch.X 2) (hz : Q.coch.d 2 z = 0) hy (x : I), M.coch.d 1 y = P.hom.f 2 z →
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy →
      tg x = Q.coch.cls 2 z hz) ∧
    (∀ x : I, ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), ∃ hy, M.coch.d 1 y = P.hom.f 2 z ∧
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy) ∧
    (∀ x : I, tg x = 0 ↔ x.1 ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H 1)) ∧
    Exact tg (P.hom.H 2)

def RankLenStatement : Prop := ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (t : R),
  Irreducible t → ∀ (L C : Cx R) (i : Hom L L) (p : Hom L C) (m N : ℕ), (∀ n x, i.f n x = t ^ m • x) → SES i p →
  L.FinGen N → C.FinLen N ∧ C.chi N = m * L.chiRk N ∧ ∀ n,
    (Module.length R (C.H n)).toNat ≤ m * Module.finrank R (L.H n) +
      (Module.length R (Submodule.torsion R (L.H n))).toNat +
      (Module.length R (Submodule.torsion R (L.H (n + 1)))).toNat ∧
    m * Module.finrank R (L.H n) ≤ (Module.length R (C.H n)).toNat

def LocaliseStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (t : R) (L V : TRep R G) (j : Pair L V),
  j.φ = MonoidHom.id G → Topology.IsOpenEmbedding j.u → (∃ e : V.V ≃ₜ V.V, ∀ v, e v = t • v) →
  (∀ v : V.V, ∃ m : ℕ, t ^ m • v ∈ LinearMap.range j.u) → ∀ n, IsLocalizedModule (Submonoid.powers t) (j.hom.H n)

end

end ReciprocityTheory.Coh
