module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WithLocPre

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAltAlt, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwist, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwistStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw




section Gen

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem eigAd_of {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {Sb eig} (h : EigAd Y Sb eig)
    (v : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) → (R.HW i (sg0 D A3.A)).H) (H : ∀ i y, Y.mj.eW i y = v i y)
    (i : Fin D.R.m) (σ k P α Rr) (hd : HkDat R Sb i k P α Rr) (hg : D.nd.goodRow σ) (y) (hy : y ∈ D.what₂.isot (i.1 + 1) σ) :
    hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e (v i y)) =
      D.what₂.embLL ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (v i y) := by
  rw [← H]
  exact h i σ k P α Rr hd hg y hy

end Gen

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}

abbrev RdTw (x : St P) (N : TwNew (Dof x)) : Type 1 :=
  R3.Read (datTw x N).R.toRealDat (datTw x N).F.lv2 (sideTw x N).p0

def jMtB (Y : RdTw x N) (μ h i y) : type_of% (x.r.Y.IL.jMt μ h i y).1 := (by with_unfolding_all exact ((Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))

def mtAd (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) {M : MtFam (Dof x)} (a : MtAd x.r.Y M) :
    MtAd Y ((fun μ j h1 h2 => { M μ j h1 h2 with })) where
  PV i := ⟨(by with_unfolding_all exact ((a.PV ((i))).ψ : _)), (by with_unfolding_all exact ((a.PV ((i))).inj : _)), (by with_unfolding_all exact ((a.PV ((i))).into : _)), (by with_unfolding_all exact ((a.PV ((i))).onto : _))⟩
  std := (by with_unfolding_all exact (a.std :))
  eW := (by with_unfolding_all exact (a.eW :))
  read μ h i y g := (by with_unfolding_all exact (((a.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))).trans
    (congrFun (H ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) ((by with_unfolding_all exact (((a.PV ((i))).ψ ((g))) : _))))) :))
  rat := (by with_unfolding_all exact (a.rat :))
  wt := (by with_unfolding_all exact (a.wt :))
  id := (by with_unfolding_all exact (a.id :))

def eWB (Y : RdTw x N) (i y) : type_of% (x.r.Y.mj.eW i y) := (by with_unfolding_all exact ((Y.mj.eW ((i)) ((y))) : _))

theorem hkDat {Sb i k Q α Rr} (h : HkDat (datTw x N).R Sb i k Q α Rr) :
    HkDat x.m.z.R ((Sb)) ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.offS :)), (by with_unfolding_all exact (h.odd :)), (by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.elt :)), (by with_unfolding_all exact (h.reps :))⟩

theorem eigAd (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) {Sb eig} (h : EigAd x.r.Y Sb eig) :
    EigAd Y ((Sb)) ((eig)) := fun i σ k Q α Rr hd hg y hy =>
  (by with_unfolding_all exact ((eigAd_of h (((eWB Y))) ((H)) ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((hkDat hd))) ((hg)) ((y)) ((hy))) : _))

-- `noncomputable` works around a Lean compiler panic (`ExplicitBoxing`, "unreachable code")
-- when generating code for this definition (seen on v4.36.0 and v4.37.0-rc1). It only skips
-- code generation; the kernel still checks everything that uses this definition.
noncomputable def ratInTw (n : InRat x.r.Y x.m.z.cG) : RatIn (w.st (oTw x N).Z).toD7
    (ratDatR (datTw x N).R (datTw x N).cG n.kKs n.hk) where
  Sb := n.In.Sb
  rho := n.In.rho
  chi := n.In.chi
  ks := n.In.ks
  fd := n.In.fd
  mk_fg := n.In.mk_fg
  hL := n.In.hL
  hs := n.In.hs
  hL_zero := n.In.hL_zero
  θ := n.In.θ
  θ_ne := n.In.θ_ne
  eig := n.In.eig
  span := (by with_unfolding_all exact ((ratIn N n.In).span : _))
  hL_int := (by with_unfolding_all exact ((ratIn N n.In).hL_int : _))

def inRat (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) (n : InRat x.r.Y x.m.z.cG) : InRat Y (datTw x N).cG where
  kKs := (by with_unfolding_all exact (n.kKs :))
  hk := (by with_unfolding_all exact (n.hk :))
  In := (by with_unfolding_all exact ((ratInTw (N := N) n) :))
  rat :=
    { hecke := fun j k Q α Rr h1 h2 hd y => (by with_unfolding_all exact ((n.rat.hecke j k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (Rr :))) h1 ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact ((hkDat hd) :))) ((by with_unfolding_all exact (y :)))) :))
      eig := (by with_unfolding_all exact ((eigAd Y H n.rat.eig) :))
      Sb_le := (by with_unfolding_all exact (n.rat.Sb_le :))
      lvl := (by with_unfolding_all exact (n.rat.lvl :))
      psi := (by with_unfolding_all exact (n.rat.psi :)) }

def inMt (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) (n : InMt x.r.Y (cfOf x) w.I.xi (QOf P)) :
    InMt Y (⟨(cfOf x).P, (cfOf x).W, (cfOf x).mu0, (cfOf x).eta, (cfOf x).chiPsi, (cfOf x).del, (cfOf x).del', (cfOf x).isMu0, (cfOf x).isEta, (cfOf x).isChi, (cfOf x).isDel, (cfOf x).isDel'⟩) w.I.xi (QOf P) where
  M := (fun μ j h1 h2 => { n.M μ j h1 h2 with })
  ad := (by with_unfolding_all exact ((mtAd Y H n.ad) :))
  mt :=
    { prod := by with_unfolding_all exact n.mt.prod
      para := by with_unfolding_all exact n.mt.para
      uni := by with_unfolding_all exact n.mt.uni
      hyp := by with_unfolding_all exact n.mt.hyp
      wt := by with_unfolding_all exact n.mt.wt
      rat := by with_unfolding_all exact n.mt.rat
      int := by with_unfolding_all exact n.mt.int
      full := by with_unfolding_all exact n.mt.full }

end GlobalTheory.HeightCounting.Up.LiTw

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAltAlt =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAltAlt", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled\n\n"}
section -- clump:auto
@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw
section Gen
variable {D : D7} (N : TwNew D)
def sideA_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding N.toD7 (N.cf cf) jE :=
  { bare := A.bare
    wdT := A.wdT
    lab := A.lab
    chr := { A.chr with }
    row := N.row A.row
    pl := { A.pl with }
    iota := A.iota
    wd := { A.wd with }
    grp := { A.grp with }
    par := { A.par with }
    au := { A.au with }
    chiT := A.chiT }
end Gen
end GlobalTheory.HeightCounting.Up.LiTw
end
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAltAlt =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAltAlt\npublic import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WithLocPre\n\n"}
section -- clump:auto
@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M

def stageAOfSwitch (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (N : TwNew D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep)
    (rep' : N.toD7.what₂.FT → NG.FinTyp N.toD7.host.E N.toD7.R.r) (e : HEq rep' rep) :
    _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL N.toD7 (N.cf cf) rep' where
  host := ⟨a.host.fr, a.host.jLL, a.host.embLL⟩
  jE := a.jE
  frame := a.frame
  A := _root_.GlobalTheory.HeightCounting.Up.LiTw.sideA_alt N a.A
  cg := _root_.UpperTheory.One.M.New.cgMk s a.cg.e (_root_.UpperTheory.One.M.New.cgGood s a.cg) (_root_.UpperTheory.One.M.New.cgSurj a.cg) a.cg.zero a.cg.loc a.cg.tw a.cg.inf a.cg.csd
  au := a.au
  row := by obtain rfl : rep' = rep := eq_of_heq e; exact a.row
  fr := ⟨a.fr.jE, a.fr.eOm, a.fr.comm⟩
  fr_jE := a.fr_jE
  pht := { a.pht with }
  depth := by obtain rfl : rep' = rep := eq_of_heq e; exact a.depth
  elem := { a.elem with }
  val := { a.val with }
  labc := a.labc
  zeta := a.zeta
  omax := a.omax
end UpperTheory.One.M
end
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwist =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwist", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw


section Gen
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}
private theorem charFrame_heq {D D' : D7} (hD : D = D')
    (a : CharFrame D) (b : CharFrame D')
    (hP : HEq a.P b.P) (hW : HEq a.W b.W) (hmu : HEq a.mu0 b.mu0)
    (heta : HEq a.eta b.eta) (hchi : HEq a.chiPsi b.chiPsi)
    (hdel : HEq a.del b.del) (hdel' : HEq a.del' b.del') : HEq a b := by
  subst D'
  cases a
  cases b
  cases eq_of_heq hP
  cases eq_of_heq hW
  cases eq_of_heq hmu
  cases eq_of_heq heta
  cases eq_of_heq hchi
  cases eq_of_heq hdel
  cases eq_of_heq hdel'
  rfl

private def reindexBase {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D D' : D7}
    {cf : CharFrame D} {cf' : CharFrame D'}
    {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    {rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r}
    (hD : D = D') (hcf : HEq cf cf') (hrep : HEq rep rep')
    (a : HeightCountingBaseData hL D cf rep) (ha : RowCusp D a.A.row) :
    {a' : HeightCountingBaseData hL D' cf' rep' // RowCusp D' a'.A.row ∧ HEq a'.A.row a.A.row} := by
  subst D'
  cases eq_of_heq hcf
  cases eq_of_heq hrep
  exact ⟨a, ha, HEq.rfl⟩

@[no_expose] def movedTwistBase {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
    (l : IntermediateLevel hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x N)) (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) :
    {a : HeightCountingBaseData hL (Dof (stTw x N m hc hh r hp)) (cfOf (stTw x N m hc hh r hp))
        (repOf (stTw x N m hc hh r hp).r.Y) //
      RowCusp (Dof (stTw x N m hc hh r hp)) a.A.row ∧ HEq a.A.row (N.row l.a.A.row)} := by
  have hD : N.toD7 = Dof (stTw x N m hc hh r hp) := (dof_oTw x N).symm
  have hcf : HEq (N.cf (cfOf x)) (cfOf (stTw x N m hc hh r hp)) := by
    with_unfolding_all
      apply charFrame_heq hD <;> rfl
  let rep := repOf r.Y
  have hrep := HEq.refl rep
  let a := _root_.UpperTheory.One.M.stageAOfSwitch trivial N l.a
    (by with_unfolding_all exact rep) (by with_unfolding_all exact e)
  with_unfolding_all
    exact reindexBase hD hcf hrep a (cusp N l.cusp)

def liftOfMovedTwist {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) (mt : InMt r.Y (cfOf (stTw x N m hc hh r hp)) w.I.xi (QOf P)) (rat : InRat r.Y m.z.cG) :
    _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp) where
  a := (movedTwistBase l m hc hh r hp e).val
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  sel := (by with_unfolding_all exact (l.sel :))
  mt := (by with_unfolding_all exact (mt :))
  rat := (by with_unfolding_all exact (rat :))
  cusp := (movedTwistBase l m hc hh r hp e).property.1
theorem li_copy_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N m hm hc hh r hp e H1 H2
  cases m
  dsimp only at hm
  subst hm
  have G2 : ∀ i y, x.r.Y.mj.eW i y = eWB (N := N) ((by with_unfolding_all exact (r.Y :))) i y := fun i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H2 ((i)) ((y)))) : _)))
  have mt : InMt r.Y (cfOf (stTw x N _ hc hh r hp)) w.I.xi (QOf P) := by
    refine
      { M := fun μ j h1 h2 => by
          with_unfolding_all exact { l.mt.M μ j h1 h2 with }
        ad :=
          { PV := fun i =>
              { ψ := by with_unfolding_all exact (l.mt.ad.PV i).ψ
                inj := by with_unfolding_all exact (l.mt.ad.PV i).inj
                into := by with_unfolding_all exact (l.mt.ad.PV i).into
                onto := by with_unfolding_all exact (l.mt.ad.PV i).onto }
            std := by with_unfolding_all exact l.mt.ad.std
            eW := by with_unfolding_all exact l.mt.ad.eW
            read := fun μ h i y g => by
              have hRead := congrFun (eq_of_heq (H1 μ h i y)) ((l.mt.ad.PV i).ψ g)
              with_unfolding_all exact (l.mt.ad.read μ h i y g).trans hRead.symm
            rat := by with_unfolding_all exact l.mt.ad.rat
            wt := by with_unfolding_all exact l.mt.ad.wt
            id := by with_unfolding_all exact l.mt.ad.id }
        mt := ?_ }
    with_unfolding_all
      exact ⟨l.mt.mt.prod, l.mt.mt.para, l.mt.mt.uni, l.mt.mt.hyp,
        l.mt.mt.wt, l.mt.mt.rat, l.mt.mt.int, l.mt.mt.full⟩
  refine ⟨liftOfMovedTwist l _ hc hh r hp e mt ?_, ?_⟩
  · with_unfolding_all exact inRat (N := N) r.Y G2 l.rat
  · constructor
    · with_unfolding_all exact (movedTwistBase l _ hc hh r hp e).property.2
    · with_unfolding_all
        exact ⟨HEq.refl l.Pq, HEq.refl (N.rat l.rat.S), HEq.refl l.rat.In.Sb,
          HEq.refl l.rat.In.hL, HEq.refl l.rat.In.eig, HEq.refl l.rat.In.θ⟩
end GlobalTheory.HeightCounting.Up.LiTw
end
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwist =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwistStatement =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwistStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwist\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.read_package_twist_heq_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.LiTw.li_copy_alt | exact _root_.GlobalTheory.HeightCounting.Up.LiTw.li_copy_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.LiTw.li_copy_alt <;> assumption)
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwistStatement =====
