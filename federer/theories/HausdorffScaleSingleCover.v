(** A single admissible covering set in the construction of Federer (1969),
    2.10.1, p. 170, and 2.10.2(1), p. 171. This supports the interval
    subdivision proof in 2.10.7, pp. 174–175, needed for 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP HausdorffLengthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_scale_single_cover]: the
    singleton-family case of the covering infimum in
    Federer 2.10.1, p. 170, with the diameter
    cost of 2.10.2(1), p. 171. *)
Lemma hausdorff_scale_single_cover (R : realType) (X : metricType R)
    (delta : \bar R) (nu : set X -> \bar R) :
  @is_metric_scale_envelope R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => extended_metric_diameter (val j)) delta nu ->
  forall A, A !=set0 -> extended_metric_diameter A<=delta -> nu A<=extended_metric_diameter A.
Proof.
move=> hn A hA hd.
pose j : @nonempty_metric_sets R X := Sub A (mem_set hA).
have h : nu A<=nonnegative_sum [set j] (fun k : @nonempty_metric_sets R X => extended_metric_diameter (val k)).
  apply: (@metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
    (fun k => val k) (fun k => extended_metric_diameter (val k)) delta nu hn
    A [set j] (countable1 j)).
  - by move=> k ->.
  - move=> x hx; exists j=> //.
rewrite nonnegative_sum_singleton in h; first exact h.
exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
Qed.
