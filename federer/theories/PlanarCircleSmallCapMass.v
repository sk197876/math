(** Federer 2.10.2(1), p. 171: supporting length bound for the portion
    of the actual unit circle in a set of sufficiently small diameter.
    A locally existing orthonormal frame and its inverse-Lipschitz
    transverse coordinate reduce to the proved real-line diameter bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations InnerProductUP Bilinear
  EuclideanInnerProduct InnerNorm InnerMetric PlanarUnitCircleGeometry
  PlanarCircleCapCoordinates MetricBiLipschitzHausdorff HausdorffMeasure
  MetricDiameterUP MetricDiameter MetricDiameterMaps MeasureUP MeasureBasic
  RealMetricBackground RealHausdorffLebesgue LebesgueDiameterBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_circle_chord_inner_product]: Federer 2.10.2(1),
    p. 171; supporting exact squared distance of two unit vectors, by
    bilinearity and symmetry from 1.7.1, p. 28. *)
Lemma unit_circle_chord_inner_product (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (a x:inner_metric_space hB):
  inner_norm hB a = 1%R -> inner_norm hB x = 1%R ->
  ((mdist a x)^+2 = 2-2*B a x)%R.
Proof.
move=>ha hx.
have haa:B a a = 1%R by rewrite -(inner_norm_sqr hB) ha expr1n.
have hxx:B x x = 1%R by rewrite -(inner_norm_sqr hB) hx expr1n.
rewrite inner_metric_distanceE inner_norm_sqr (bilBl (inner_bilinear hB))
  !(bilBr (inner_bilinear hB)) (inner_symmetric hB x a) haa hxx.
ring.
Qed.

(** Source for [small_planar_circle_intersection_length]: Federer
    2.10.2(1), p. 171; supporting cap bound in the fixed-cutoff example.
    The actual source set need not be measurable or nonempty. Its diameter
    condition forces a positive cap coordinate, rather than assuming one. *)
Theorem small_planar_circle_intersection_length (R:realType)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))) (delta d:R):
  (0<delta)%R -> (delta<=1)%R -> (0<=d)%R ->
  (d^+2<=2-2*delta)%R -> (extended_metric_diameter S<=d%:E) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (@planar_unit_circle R `&` S)<=delta^-1%R%:E*extended_metric_diameter S.
Proof.
move=>hd hd1 hd0 hSquare hDiam.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose T:set X:=@planar_unit_circle R `&` S.
case:(pselect (T !=set0))=>[hT|hEmpty].
- have [a [ha hSa]]:=hT.
  have [e hf]:=planar_circle_frame_exists ha.
  pose q:=fun x:X=>(euclidean_inner_product e x:real_line_metric R).
  pose K:set X:=[set x|inner_norm (@euclidean_inner_productP R 2) x = 1%R /\
    (delta<=euclidean_inner_product a x)%R].
  have hTK:T `<=` K.
    move=>x [hx hSx]; split=>//.
    have hDist:(mdist a x<=d)%R.
      have hh:=le_trans (metric_diameter_upper (extended_metric_diameter_specification S) hSa hSx) hDiam.
      by move:hh; rewrite lee_fin.
    have hSq:((mdist a x)^+2<=d^+2)%R by rewrite (ler_sqr (mdist_ge0 _ _) hd0).
    have hChord:=unit_circle_chord_inner_product ha hx.
    rewrite hChord in hSq; clear -R hSq hSquare; nra.
  have hL:=planar_unit_cap_projection_bilipschitz hf hd hd1.
  have hMass:=(@metric_bilipschitz_hausdorff_bounds R X
    [the metricType R of real_line_metric R] K q delta^-1%R (0%R:X) 1 T hL hTK).2.
  have hImage:q @` T !=set0 by exists (q a); exists a.
  have hReal:@hausdorff_measure R [the metricType R of real_line_metric R] 1 (q @` T)<=
      extended_metric_diameter (q @` T).
    rewrite real_hausdorff_measure_one_lebesgue; exact:lebesgue_scalar_diameter_bound hImage.
  have hProjection:=extended_metric_diameter_nonexpanding
    (planar_frame_projection_nonexpanding hf) T.
  have hSource:extended_metric_diameter T<=extended_metric_diameter S.
    apply:extended_metric_diameter_mono; by move=>x [_ hx].
  rewrite expr1 in hMass.
  apply:le_trans hMass _; apply:lee_wpmul2l; first by rewrite lee_fin invr_ge0; exact:ltW hd.
  exact:le_trans hReal (le_trans hProjection hSource).
- have hZero:T=set0 by apply/seteqP; split=>x // hx; exfalso; apply:hEmpty; exists x.
  change (@hausdorff_measure R X 1 T<=delta^-1%R%:E*extended_metric_diameter S).
  rewrite hZero (measure_empty (@hausdorff_measure_is_measure R X 1)).
  apply:mule_ge0; first by rewrite lee_fin invr_ge0; exact:ltW hd.
  exact:metric_diameter_nonnegative (extended_metric_diameter_specification S).
Qed.
