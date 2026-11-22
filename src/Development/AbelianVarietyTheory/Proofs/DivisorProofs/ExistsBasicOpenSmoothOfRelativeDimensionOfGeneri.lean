module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SmoothRelDim

theorem smoothOfRelativeDimension_of_generic (R : Type) [CommRing R] [IsDomain R] (X : Over (Sp R))
    [Smooth X.hom] (K : Type) [Field K] (e : R →+* K) (he : Function.Injective e) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e))) :
    SmoothOfRelativeDimension g X.hom := by
  have hdom : IsDominant (spMap e) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by change RingHom.ker e ≤ _; rw [(RingHom.injective_iff_ker_eq_bot e).1 he]; exact bot_le)⟩
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have : UniversallyOpen X.hom := UniversallyOpen.of_flat X.hom
  have key : ∀ x, n x = g := fun x => by
    have ho : IsOpen (X.hom.base '' (W x : Set X.left)) := X.hom.isOpenMap _ (W x).isOpen
    obtain ⟨s, ⟨y, hyW, hy⟩, t, rfl⟩ :=
      hdom.denseRange.inter_open_nonempty _ ho ⟨_, x, hW x, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback y t hy
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback X.hom (spMap e)) (hd x) hg z (hz1 ▸ hyW)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => key x ▸ hd x

end GlobalTheory.SmoothRelDim
