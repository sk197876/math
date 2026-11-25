(** Federer (1969), 3.2.13, p. 251: intrinsic sphere
    integration agrees with the subset Hausdorff integral. The
    actual graph, including signed infinite values, is preserved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal
  topology subtype_topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HausdorffMeasure
  UnitSphereSpace EuclideanSphereMeasurable OpenSubspaceMeasure MeasureUP MeasurePushforward MeasureRestriction
  RestrictedIntegralIdentity InjectivePushforwardIntegral PartialFunctionUP PartialFunctionPrecomposition
  MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_sphere_intrinsic_integral_iff]: the
    Hausdorff measure over S^(m-1) in the invariant-measure step
    is the same measure used in the printed coordinate moment,
    Federer 3.2.13, p. 251. *)
Theorem unit_sphere_intrinsic_integral_iff (R:realType) m (w:R_n R m->R) a:
  is_measure_integral (@unit_sphere_hausdorff_measure R m)
    (real_total_integrand (fun u:euclidean_unit_sphere_space R m=>w (set_val u))) a <->
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1]
    (real_total_integrand w) a.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose S:=@euclidean_unit_sphere_set R m.
pose H:=@hausdorff_measure R X (m-1).
have hInj:injective (set_val:set_type S->X) by move=>u v; exact:val_inj.
have hPush:=@injective_pushforward_integral_iff R [the choiceType of set_type S]
  [the choiceType of X] (@unit_sphere_hausdorff_measure R m)
  (@unit_sphere_hausdorff_is_measure R m) set_val (real_total_integrand w) hInj a.
have hMap:measure_pushforward (set_val:set_type S->X) (@unit_sphere_hausdorff_measure R m)=
    measure_restrict H S:=@open_subspace_measure_pushforward R X S H.
rewrite hMap in hPush.
have hRestr:=@restricted_integral_zero_extension_iff R X H (@hausdorff_measure_is_measure R X (m-1))
  S (real_total_integrand w) a (@euclidean_norm_sphere_hausdorff_measurable R m (m-1) 1).
exact:iff_trans hPush hRestr.
Qed.
