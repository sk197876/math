(** Federer (1969), 3.2.13, p. 250: the
    first polar integral equality in source dimensions
    greater than one. The one-dimensional case is
    a separate area-formula obligation. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions LebesgueScalarMeasure RadialSphereIntegral RadialScalarIntegral
  ScalarPositiveRayIntegral HausdorffMeasure PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureConullZeroIntegral
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_sphere_integral_negative_zero]: the
    sphere of a negative radius is empty in
    the first formula of Federer 3.2.13, p. 250.
    Its subset integral is zero for any original
    partial integrand and every natural Hausdorff degree. *)
Lemma radial_sphere_integral_negative_zero (R:realType) m u (r:R):
  (r<0)%R ->partial_function_graph (@radial_sphere_integral R m u) r 0.
Proof.
move=>hr; apply/radial_sphere_integral_graph.
pose hm:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1).
apply:(measure_almost_zero_integral hm).
apply:(@measure_almost_everywhere_mono R _ _ hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
apply/partial_function_zero_extension_graph; right; split; last by [].
move=>hx; have hN:=inner_norm_nonnegative (@euclidean_inner_productP R m) x.
rewrite hx in hN; by move:hr; rewrite ltNge hN.
Qed.

(** Source for [radial_polar_first_high_dimension]: the
    first displayed polar integration formula in
    Federer 3.2.13, p. 250, for m>1.
    Both integrals exist with the same actual
    value; signed infinite values and the exact
    fibre-integrability domain are retained. *)
Lemma radial_polar_first_high_dimension (R:realType) m (g:R_n R m->R):
  (1<m)%N ->is_measure_integrable (@euclidean_lebesgue_measure R m) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand g) a /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
      (radial_sphere_integral (real_total_integrand g)) a.
Proof.
move=>hm hg; have [a [hI hRadial]]:=radial_scalar_integral_high_dimension hm hg.
exists a; split=>//.
exact (scalar_positive_ray_integral (@radial_sphere_integral_negative_zero R m _) hRadial).
Qed.
