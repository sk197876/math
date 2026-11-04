(** Federer (1969), 3.2.46, p. 282: the
    target Riemannian volume density restores the frozen
    complementary fibre integral. Local control is needed
    only where the actual fibre is nonempty; the full
    original target and infinite fibre masses remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianChartReference
  RiemannianChartVolumeDensity RiemannianChartVolumeIntegral RiemannianVolumeIdentification
  NonnegativeLocalDensityIntegralBounds MappingMultiplicity HausdorffMeasure
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureIntegralUP
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coarea_target_density_bounds]:
    restore the actual target volume in the local
    coarea argument of 3.2.46, p. 282.
    Density control on the actual represented image
    suffices; no global bound, finite target volume,
    rank or independent integrability premise is assumed. *)
Theorem riemannian_coarea_target_density_bounds (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (L : {linear R_n R m -> R_n R m})
    (S : set (riemannian_metric_space hg))
    (hpTarget : 0<=n%:R :> R) (s d : R) a :
  0<s -> 0<d ->
  (forall x, S x -> riemannian_chart_volume_density hh (f x)<=s*d /\
    d<=s*riemannian_chart_volume_density hh (f x)) ->
  is_measure_integral (@riemannian_chart_reference R n B h hh)
    (partial_function_total (fun y : riemannian_metric_space hh=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n)
      ((fun x : riemannian_metric_space hg=>L (val x)) @` mapping_fibre f S y)
        : extended_real_line R))) a ->
  exists b, is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
    (partial_function_total (fun y : riemannian_metric_space hh=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n)
      ((fun x : riemannian_metric_space hg=>L (val x)) @` mapping_fibre f S y)
        : extended_real_line R))) b /\
    (b<=s%:E*(d%:E*a))%E /\ (d%:E*a<=s%:E*b)%E.
Proof.
move=> hs hd hDensity hIntegral.
pose X := [the choiceType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose phi := @riemannian_chart_reference R n B h hh.
pose mu := riemannian_hausdorff_measure hh n%:R hpTarget.
pose u := fun y : Y=>(@hausdorff_measure R E (m-n)
  ((fun x : X=>L (val x)) @` mapping_fibre f S y) : extended_real_line R).
apply:(@nonnegative_local_density_integral_bounds R Y phi mu
  (riemannian_chart_volume_density hh) u s d a
  (@riemannian_chart_reference_is_measure R n B h hh)
  (@riemannian_volume_density_identification R n B h hh hpTarget)
  (@riemannian_chart_density_measurable R n B h hh)).
- move=> y; exact (ltW (@riemannian_chart_volume_density_positive R n B h hh y)).
- move=> y; exact (@measure_nonnegative R E (@hausdorff_measure R E (m-n))
    (@hausdorff_measure_is_measure R E (m-n))
    ((fun x : X=>L (val x)) @` mapping_fibre f S y)).
- exact hs.
- exact hd.
- move=> y; case:(pselect (exists x, S x /\ f x=y))=> [[x [hx <-]]|hEmpty].
  + right; exact:hDensity x hx.
  + left.
    have hFibre : mapping_fibre f S y=set0.
      apply/seteqP; split; last by move=> x [].
      move=> x [hx hxy]; exfalso; apply:hEmpty; by exists x.
    rewrite /u hFibre image_set0; exact:measure_empty (@hausdorff_measure_is_measure R E (m-n)).
- exact hIntegral.
Qed.
