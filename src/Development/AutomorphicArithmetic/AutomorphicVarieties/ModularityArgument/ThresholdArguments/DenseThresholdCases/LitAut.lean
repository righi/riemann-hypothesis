module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
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

@[expose] public section




section
namespace GlobalTheory.Mem.LiteralAutomorphy
open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published
structure LitLocAlt : Prop where
  bz : BernsteinZelevinskyFiniteness
  bern : BernsteinUnitaryProductIrreducible
  geo : GeometricLemma
  zel : ZelevinskyPolynomialRing
  disj : TotallyDisjointProductIrreducible
  mp : MoyPrasadJacquetIso
  temp : TemperedProductOfSquareIntegrable
  seg : EssSquareIntegrableSegments
  sq : SquareIntegrableSegment
  gen : GenericUnlinkedGL
  multi : LanglandsMultisegments
  exh : LanglandsExhaustionGL
  cos : StandardCosocleGL
  conv : LocalConverseGL
  dzi : DepthZeroInduction
  brauer : BrauerDegreeZero
  chev : ChevalleyUnits
  green : GreenRegularCharacters
structure LiteratureAutomorphyHypothesis : Prop where
  decay : CuspRapidDecay
  hc : HarishChandraFinite
  fin : AutomorphicFormsFiniteGL
  js : JacquetShalika
  cusp : CuspidalSpectrumGL
  bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN
  gk : GelfandKazhdanDual
  gal : _root_.UpperTheory.V.Z.Win.RowT
  pur : ClozelPurity
  coh : ClozelCohomological
  art : GlobalArtinReciprocity
  ray : RayClassFieldSt
  chA : HeckeLAdicCharacterAbove
  chW : AlgebraicCharacterWD
  berger : DeRhamPotSemistable
structure LiteratureCMHypothesis : Prop where
  gm : GrothendieckDeformation
  dr : AbelianDeRham
  dual : AbelianDualCrystal
  per : PeriodComparison
  gmp : GaussManinPeriods
  cm : EllipticMainTheoremCM
  hj : HilbertClassFieldJ
  dri : SiegelKlingenDeligneRibet
  pz : PartialZetaFunctionalEquation
  fe : HeckeTateFunctionalEquation
structure LiteratureRankNHypothesis : Prop where
  loc : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt
  aut : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis
  coh : LitCoh
  cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis
end GlobalTheory.Mem.LiteralAutomorphy
end
