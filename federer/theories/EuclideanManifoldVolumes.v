(** Federer (1969), 3.2.28(2)–(5), pp. 265–267:
    abbreviations for actual Hausdorff volumes, with
    their proved coarea and area relations. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerMetric OrthogonalMaps
  EuclideanHomInnerCharts ExteriorGrading ExteriorNorm InnerExterior InnerExteriorPositivity AssociatedSubspace
  InnerSymmetricPositivity EuclideanExteriorFrameFibres EuclideanExteriorCoareaVolume EuclideanSpecialOrthogonalMeasure
  EuclideanGrassmannSquare EuclideanGrassmannAreaVolume EuclideanManifoldMeasureFiniteness
  HausdorffMeasure MeasureUP RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_stiefel_volume]: the actual
    H^(m(2n-m-1)/2) mass of O(n,m), Federer
    3.2.28(5), p. 267, in the specified
    Hilbert Hom metric; this is an abbreviation,
    not a separately normalized quotient measure. *)
Definition euclidean_stiefel_volume (R:realType) n m:=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R m n)) (m*(2*n-m-1)%/2)
    [set g|is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g)].

(** Source for [euclidean_oriented_grassmann_volume]: the
    actual H^(m(n-m)) mass of the simple unit
    realization Go(n,m), Federer 3.2.28(2),(5),
    pp. 264–265,267. *)
Definition euclidean_oriented_grassmann_volume (R:realType) n m:=
  @hausdorff_measure R (inner_metric_space (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)) (m*(n-m))
    [set x|simple x /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) x= 1%R].

(** Source for [euclidean_grassmann_volume]: the actual
    H^(m(n-m)) mass of the square realization of
    G(n,m), Federer 3.2.28(4),(5), p. 267. *)
Definition euclidean_grassmann_volume (R:realType) n m:=
  let E:=exterior_power (R_n R n) m in
  let B:=@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  let hB:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  @hausdorff_measure R (inner_metric_space (@symmetric_inner_productP R E B hB 2)) (m*(n-m))
    (@euclidean_grassmann_square_set R n m).

(** Source for [euclidean_stiefel_volume_exterior]: the
    first displayed coarea volume identity of Federer
    3.2.28(2), p. 265. The factor two is
    proved by the orientation-reversing involution on
    O(m), with positive m explicit. *)
Theorem euclidean_stiefel_volume_exterior (R:realType) n m:
  (0<m)%N ->(m<=n)%N ->
  (2:R)%:E*euclidean_stiefel_volume R n m=
    euclidean_stiefel_volume R m m*euclidean_oriented_grassmann_volume R n m.
Proof.
move=>hm hmn.
have hCoarea:=@euclidean_exterior_coarea_volume R m n hm hmn.
have hHalf:=@euclidean_special_orthogonal_half_measure R m hm (m*(m-1)%/2)%N.
have hDegree : (m * (2 * m - m - 1) %/ 2 = m * (m - 1) %/ 2)%N.
  by rewrite mul2n -addnn addKn.
rewrite /euclidean_stiefel_volume /euclidean_oriented_grassmann_volume hCoarea hDegree hHalf muleA.
reflexivity.
Qed.

(** Source for [euclidean_grassmann_volume_orientation]: the
    actual twofold area relation in Federer 3.2.28(4),
    p. 267. No quotient measure is substituted
    for either Hausdorff measure. *)
Theorem euclidean_grassmann_volume_orientation (R:realType) n m:
  (0<m)%N ->(m<=n)%N ->
  euclidean_oriented_grassmann_volume R n m=(2:R)%:E*euclidean_grassmann_volume R n m.
Proof. exact:(@euclidean_grassmann_area_volume R m n). Qed.

(** Source for [euclidean_stiefel_volume_finite]: compact
    smooth O(n,m) has finite actual Hausdorff mass,
    supporting the volume evaluation in Federer
    3.2.28(5), p. 267. *)
Theorem euclidean_stiefel_volume_finite (R:realType) n m:
  euclidean_stiefel_volume R n m < +oo.
Proof.
have [hRect _]:=@euclidean_stiefel_measure_rectifiable R m n.
exact hRect.2.
Qed.
