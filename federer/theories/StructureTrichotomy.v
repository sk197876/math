(** Federer (1969), 3.3.4, pp. 288–292: the complete three-way
    alternative for the original Grassmann probability in all dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import HomInner HomSpaceTopology GrassmannHomogeneousSpace FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanGrassmannProbability EuclideanGrassmannProbabilityUP
  StructureConeUP StructurePlaneGrowth StructureZeroPlaneAlternative
  StructureFullPlaneAlternative StructureTrichotomyPositiveCodimension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CompactGroupHomogeneousMeasures
  CovariantIntegralUP SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_trichotomy]: Federer 3.3.4, pp. 288–292.
    For every 0<=m<=n, original Suslin A, original centre a, and outer
    measure phi measuring closed sets, gamma_(n,n-m)-almost every V has
    either some positive radial cutoff with ordinary zero aperture
    growth, infinite upper aperture growth at every positive cutoff,
    or original punctured affine-plane accumulation at a. Infinite
    numerator values and both dimension endpoints are retained. All
    projective, group and coordinate auxiliaries are local proof data. *)
Theorem structure_trichotomy (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  is_structure_measure phi ->is_suslin_set R A ->
  @measure_almost_everywhere R
    [the choiceType of grassmann_space
      (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
      (@coordinate_basisP R (n-m)) (@coordinate_basisP R n)]
    (@euclidean_grassmann_probability R n (n-m) (leq_subr m n))
    [set V|structure_plane_trichotomy m phi A a V].
Proof.
pose k:=(n-m)%N.
have hDim:(m+k)%N=n by rewrite /k addnC subnK.
move:phi A a; rewrite -hDim=>phi A a hPhi hA.
case hk:(k==0).
- move/eqP:hk=>hk; move:phi A a hPhi hA; rewrite hk addn0=>phi A a hPhi hA.
  have hSpec:=@euclidean_grassmann_probability_specification R m (m-m) (leq_subr m m).
  have [J [hMono hInvariant hMeasure hRep hRegular]]:=hSpec.1.
  apply:(measure_almost_everywhere_mono hMeasure _ (measure_almost_everywhere_true hMeasure))=>V _.
  left; move:V; rewrite subnn=>V.
  exact:structure_zero_plane_zero_growth hPhi.1.
- have hkPositive:(0<k)%N by rewrite lt0n hk.
  exact:(@structure_trichotomy_positive_codimension R m k (leq_addr k m) phi A a hkPositive hPhi hA).
Qed.
