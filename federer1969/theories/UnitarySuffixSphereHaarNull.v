(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    pp. 329–330: original suffix-sphere null sets pull back
    to null sets for every original suffix Haar measure.
    Apply the existing exact sphere chart and orbit comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import PointedHolomorphicPullbackComposition HolomorphicRotatedGermIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import ComplexScalarLaws OrthonormalFamilies HermitianComplexLinearity
  FiniteCoordinates StandardHermitianCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  UnitaryCoordinateFixing UnitaryFixingSphereAction UnitaryFixingSphereHaarNull HolomorphicSuffixSphereCoordinates
  MetricSubsetBackground HaarIntegralUP HausdorffMeasure OrdinalCoordinateTail.
Import Order.TTheory Num.Theory ComplexScalarTheory.
Section SuffixHaar.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@orthogonal_group R XR B hB (n+n) eR heR).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation M:=(@holomorphic_germ_metric R X NX hNXR 0).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH (n+n) eR heR g).
Local Notation P:=(fun g:U=>@holomorphic_unitary_germ_map R X H hH (n+n) eR heR g).
Variable hON:orthonormal_family H e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i j,omega i (e j)=if i==j then 1 else 0.
Variable m:'I_n.
Variable hMN:((m:nat)<=n)%N.
Local Notation k:=(n-m)%N.
Local Notation J:=([set i:'I_n|(i<m)%N]).
Local Notation F:=(@holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.

Variables (mulF:F->F->F) (invF:F->F) (unitF:F).
Variable hF:is_subgroup_restriction mulU invU unitU F mulF invF unitF.
(** Source for [unitary_suffix_sphere_haar_coordinate_null]: exact
    original suffix coefficients and every original left Haar measure,
    3.4.12, p. 339. *)
Theorem unitary_suffix_sphere_haar_coordinate_null (mu:set F->\bar R)
    (D:set (R_n R (k+k))):
  is_left_haar_measure mulF mu ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (k+k))) (k+k-1)
    [set y|inner_norm (@euclidean_inner_productP R (k+k)) y= 1 /\D y]=0%:E ->
  mu [set q:F|D (complex_real_coordinates
    [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (mapg (set_val q) (e m))])]=0%:E.
Proof.
move=>hMu hNull.
have [SR [PR [hCancel [hDistance [hImage hCoordinates]]]]]:=
  @holomorphic_suffix_sphere_coordinate_witnesses R X H hH n e he hON omega hDual m hMN.
pose sphere:=@unitary_fixing_sphere R X H hH n e J.
pose MS:=[the metricType R of metric_subset sphere].
have hAxis:sphere (e m).
  split.
  - apply:inner_norm_value;first exact:ler01.
    by rewrite expr1n /hermitian_real_part hON eqxx -(rmorph1 (ComplexScalars.embed R)) re_embed.
  - move=>i hi;change (is_true ((i:nat)<(m:nat))%N) in hi;rewrite hON.
    have hDifferent:m!=i by apply/eqP=>hEqual;by rewrite -hEqual ltnn in hi.
    by rewrite (negbTE hDifferent).
pose axis:MS:=exist _ (e m) (mem_set hAxis).
have hPositive:(0<k+k)%N by rewrite addn_gt0 /k subn_gt0 (ltn_ord m).
have hOrbit:=@unitary_fixing_sphere_haar_coordinate_null R X H hH (n+n) eR heR n e J
  mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF (k+k)%N hPositive
  SR PR hCancel hDistance hImage mu axis D hMu hNull.
have hValues x:PR x=complex_real_coordinates
    [ffun i=>omega (ordinal_coordinate_tail_index hMN i) x].
  by rewrite -(hCoordinates x) complex_from_real_coordinatesK.
have hSets:[set q:F|D (PR (val (@unitary_fixing_sphere_action R X H hH (n+n) eR heR n e J q axis)))]=
    [set q:F|D (complex_real_coordinates
      [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (mapg (set_val q) (e m))])].
  apply:funext=>q.
  change (D (PR (mapg (set_val q) (e m)))=D (complex_real_coordinates
    [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (mapg (set_val q) (e m))])).
  by rewrite hValues.
by rewrite -hSets.
Qed.
End SuffixHaar.
