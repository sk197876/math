(** Federer (1969), 3.2.33, p. 270: every original-domain
    fibre has zero (m-mu)-dimensional Hausdorff measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanSliceDifferentials RealOpenIntervals LipschitzUP
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanHausdorffLebesgue HausdorffMeasure HausdorffDimensionDrop
  HausdorffLipschitzImages MeasureUP MeasureBasic ScalarCylinderMapUP ScalarCylinderFibres EuclideanOpenUnitCube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_unit_cube_higher_mass_zero]:
    the k-dimensional fibre cube has zero H^(k+1) measure,
    supporting Y=empty in Federer 3.2.33, p. 270.
    Its natural H^k mass is one by 2.10.35,
    p. 197, and the cube volume formula; then 2.10.2(1)
    applies. In degree zero the cube is one point of
    positive H^0 mass, not a null source. *)
Lemma euclidean_open_unit_cube_higher_mass_zero (R:realType) k:
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) k.+1
    (@euclidean_open_unit_cube R k)= 0%E.
Proof.
apply:(hausdorff_finite_mass_higher_degree_zero (ltnSn k)).
rewrite (euclidean_hausdorff_spherical_lebesgue (@euclidean_open_unit_cube R k)).1.
change (is_true ((euclidean_lebesgue_measure k [set x:R_n R k|forall i,(0<x i<1)%R]) < +oo)%E).
by rewrite euclidean_unit_cube ltry.
Qed.

(** Source for [scalar_cylinder_fibre_hausdorff_zero]: all
    fibres in the original unit cube have zero H^(m-mu)
    mass, Federer 3.2.33, p. 270. The exact fibre
    cube is included isometrically in the source space;
    the Lipschitz image bound retains k= 0 and mu= 0. *)
Theorem scalar_cylinder_fibre_hausdorff_zero (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->
  (forall u v,real_open_interval 0 1 u ->real_open_interval 0 1 v ->u<v ->g u<g v) ->
  forall y,@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) k.+1
    [set x|euclidean_open_unit_cube x /\F x=y]= 0%E.
Proof.
move=>hF hStrict y.
pose A:set (R_n R ((mu+1)+k)):=[set x|euclidean_open_unit_cube x /\F x=y].
change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) k.+1 A= 0%E).
case:(pselect (exists x,A x))=>[[x [hx hFx]]|hEmpty].
- have hEq:A=[set z|euclidean_open_unit_cube z /\F z=F x] by rewrite /A hFx.
  rewrite hEq (scalar_cylinder_fibre_cube hF hStrict hx).
  pose J (z:inner_metric_space (@euclidean_inner_productP R k)):
      inner_metric_space (@euclidean_inner_productP R ((mu+1)+k)):=
    euclidean_block_join (@euclidean_first_block R (mu+1) k x,z).
  have hLip:is_metric_lipschitz_bound setT J 1.
    split; first exact:ler01.
    move=>z w _ _; by rewrite /J euclidean_fixed_first_block_distance mul1r.
  have hBound:=hausdorff_lipschitz_image_bound k.+1 hLip (@euclidean_open_unit_cube R k).
  rewrite euclidean_open_unit_cube_higher_mass_zero expr1n mul1e in hBound.
  apply/eqP; rewrite eq_le (measure_nonnegative (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) k.+1)) andbT.
  exact hBound.
- have hEq:A=set0.
    apply/seteqP; split=>x hx; last by case:hx.
    exfalso; apply:hEmpty; by exists x.
  change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) k.+1 A= 0%E).
  by rewrite hEq (measure_empty (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) k.+1)).
Qed.

(** Source for [scalar_cylinder_positive_fibre_set_empty]:
    the printed conclusion Y=empty in Federer 3.2.33,
    p. 270. In fact every fibre, including target points
    outside the image, has zero required mass. *)
Corollary scalar_cylinder_positive_fibre_set_empty (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->
  (forall u v,real_open_interval 0 1 u ->real_open_interval 0 1 v ->u<v ->g u<g v) ->
  [set y| (0< @hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) k.+1
    [set x|euclidean_open_unit_cube x /\F x=y])%E]=set0.
Proof.
move=>hF hStrict; apply/seteqP; split=>y hy; last by case:hy.
change (is_true ((0< @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k)))
  k.+1 [set x|euclidean_open_unit_cube x /\F x=y])%E)) in hy.
by rewrite (scalar_cylinder_fibre_hausdorff_zero hF hStrict y) ltxx in hy.
Qed.
