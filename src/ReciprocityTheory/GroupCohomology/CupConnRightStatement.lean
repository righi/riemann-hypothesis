module

public import ReciprocityTheory.GroupCohomology.ContinuousContractNth

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

def LESStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (i : Hom A B) (p : Hom B C), SES i p →
  (∃ δ, IsConn i p δ ∧ LES i p δ) ∧ ∀ δ δ', IsConn i p δ → IsConn i p δ' → δ = δ'

def TowerStatement : Prop := ∀ (R : Type u) [CommRing R] (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m))
  (L : Cx R) (π : ∀ m, Hom L (A m)), IsTowerLim A τ L π → ∀ n,
  (∀ y : ∀ m, (A m).H n, (∀ m, (τ m).H n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).H n x = y m) ∧
  ((∀ k, n = k + 1 → ∀ m, IsArtinian R ((A m).H k)) → ∀ x : L.H n, (∀ m, (π m).H n x = 0) → x = 0)

def LowStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G),
  (∀ n, ∃ e : M.H n ≃ₗ[R] Hn M.rho n, ∀ x hx, ∃ hz : x.1 ∈ Zn M.rho n,
    e (M.coch.cls n x hx) = Submodule.Quotient.mk ⟨x.1, hz⟩) ∧
  (∃ e : M.H 0 ≃ₗ[R] H0 M.rho, ∀ x hx, (e (M.coch.cls 0 x hx) : M.V) = x.1 ![]) ∧
  (∃ e : M.H 1 ≃ₗ[R] H1 M.rho, ∀ x hx, ∃ hz : (fun g => x.1 ![g]) ∈ Z1 M.rho,
    e (M.coch.cls 1 x hx) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
  ∃ e : M.H 2 ≃ₗ[R] H2 M.rho, ∀ x hx, ∃ hz : (fun g : G × G => x.1 ![g.1, g.2]) ∈ Z2 M.rho,
    e (M.coch.cls 2 x hx) = Submodule.Quotient.mk ⟨_, hz⟩

def AdmStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A B C : TRep R G) (i : Pair A B) (p : Pair B C),
  admitted i p → SES i.hom p.hom

def GroupSectionStatement : Prop := ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (U : Subgroup G), IsClosed (U : Set G) →
  ∃ r : G → U, Continuous r ∧ r 1 = 1 ∧ ∀ (x : U) g, r (x * g) = x * r g

def InfResStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal]
  (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P →
  Injective (P.hom.H 1) ∧ Exact (P.hom.H 1) ((Pair.res M N.subtype continuous_subtype_val).hom.H 1) ∧
  ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) → (∀ m, c.u m = M.rho s m) →
    ∀ n x, c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n x) =
      (Pair.res M N.subtype continuous_subtype_val).hom.H n x

def FiveTermStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → ∀ I : Submodule R ((M.resSub N).H 1),
  (∀ x, x ∈ I ↔ ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H 1 x = x) →
  ∃ tg : I →ₗ[R] Q.H 2, (∀ x : I, tg x = 0 ↔
      x.1 ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H 1)) ∧ Exact tg (P.hom.H 2)

def CupStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (b : Pairing M N P),
  (∀ p q f f' (g : Fin (p + q + 1) → G), dn P.rho (p + q) (cupFun b p q f f') g =
    cupFun b (p + 1) q (dn M.rho p f) f' (fun i => g (i.cast (by omega))) +
      (-1 : R) ^ p • cupFun b p (q + 1) f (dn N.rho q f') g) ∧
  (∃ cup, IsCup b cup) ∧ ∀ cup cup', IsCup b cup → IsCup b cup' → cup = cup'

def LimRepStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : ℕ → TRep R G) [∀ m, DiscreteTopology (A m).V]
  (τ : ∀ m, Pair (A (m + 1)) (A m)) (L : TRep R G) (π : ∀ m, Pair L (A m)),
  (∀ m, (τ m).φ = MonoidHom.id G ∧ (π m).φ = MonoidHom.id G ∧ Surjective (τ m).u ∧
    ∀ x, (τ m).u ((π (m + 1)).u x) = (π m).u x) →
  Topology.IsEmbedding (fun (x : L.V) m => (π m).u x) →
  (∀ y : ∀ m, (A m).V, (∀ m, (τ m).u (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).u x = y m) →
  IsTowerLim (fun m => (A m).coch) (fun m => (τ m).hom) L.coch fun m => (π m).hom

def ModTStatement : Prop := ∀ (R : Type u) [CommRing R] (A C : Cx R) (i : Hom A A) (p : Hom A C) (t : R) δ,
  (∀ n x, i.f n x = t • x) → SES i p → IsConn i p δ → ∀ n,
  (∀ x, p.H n x = 0 ↔ ∃ y, x = t • y) ∧ Exact (p.H n) (δ n) ∧ ∀ x, x ∈ LinearMap.range (δ n) ↔ t • x = 0

def FinGenStatement : Prop := ∀ (R : Type u) [CommRing R] (t : R) [IsAdicComplete (Ideal.span {t}) R]
  (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)),
  IsTowerLim A τ L π → (∀ n (x : L.X n), t • x = 0 → x = 0) →
  (∀ m n (x : L.X n), (π m).f n x = 0 ↔ ∃ y, x = t ^ (m + 1) • y) →
  (∀ n, IsFiniteLength R ((A 0).H n)) → ∀ n, Module.Finite R (L.H n) ∧ ∀ m, IsFiniteLength R ((A m).H n)

end ReciprocityTheory.Coh
