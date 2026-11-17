(** Federer (1969), 3.4.8(13), p. 328:
    independent laws for the bounded representative and
    its uniform Hausdorff diameter estimate. Existence and
    the analytic dimension comparison are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter CoveringFamilyUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_uniform_hausdorff_growth]: the finite
    supremum of Hausdorff mass divided by diameter
    to the m-th power in 3.4.8(13),
    p. 328, expressed by a finite nonnegative
    common coefficient. The all-subset estimate also treats
    zero diameter without dividing by zero. *)
Record is_uniform_hausdorff_growth (R:realType) (X:metricType R) m (S:set X) (c:R):Prop:={
  (** Source for [uniform_hausdorff_growth_bounded]: the bounded
      representative selected in the proof of
      3.4.8(13), p. 336. *)
  uniform_hausdorff_growth_bounded:metric_set_bounded S;
  (** Source for [uniform_hausdorff_growth_coefficient]: a finite
      nonnegative coefficient for the displayed growth bound,
      3.4.8(13), pp. 328, 336. *)
  uniform_hausdorff_growth_coefficient:(0<=c)%R;
  (** Source for [uniform_hausdorff_growth_bound]: the final
      all-subset diameter inequality in 3.4.8(13), p. 336,
      including nonmeasurable and zero-diameter subsets. *)
  uniform_hausdorff_growth_bound:forall T:set X,T `<=` S ->
    (@hausdorff_measure R X m T<=c%:E*(extended_metric_diameter T)^+m)%E
}.
