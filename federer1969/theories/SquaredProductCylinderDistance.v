(** Federer (1969), 3.2.36, pp. 272--273:
    the first-factor distance is the actual
    distance to the entire first-factor cylinder. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import SquaredMetricProductUP SquaredMetricProductLaws MetricCartesianProductUP
  MetricSetDistanceUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [squared_product_cylinder_distance]: the
    actual first-factor distance f(y,z)=dist(y,P)
    in Federer 3.2.36, pp. 272--273,
    is distance to P times the whole
    second factor. Nonexpansion gives the
    lower bound; keeping the second coordinate
    fixed and the first-slice isometry prove
    the greatest-lower-bound law. This supports
    the application of 3.2.34's actual unit-
    Jacobian proof on the possibly unbounded
    closed cylinder, without an assumed
    derivative or selected nearest-point field. *)
Lemma squared_product_cylinder_distance (R:realType) (Z X Y:metricType R)
    (pair:X->Y->Z) first second (hp:is_squared_metric_product pair first second)
    (A:set X) (d:X->R):
  is_metric_set_distance A d ->
  is_metric_set_distance [set z|A (first z)] (fun z=>d (first z)).
Proof.
move=>hD.
have hCartesian:=squared_metric_product_cartesian hp.
constructor.
- move=>z w hw.
  have hLower:=@metric_set_distance_lower R X A d hD (first z) (first w) hw.
  have hProjection:mdist (first z) (first w)<=mdist z w.
    have h:=(metric_product_first_nonexpanding hCartesian).2 z w I I.
    by rewrite mul1r in h.
  exact:le_trans hLower hProjection.
- move=>z r hBound.
  apply:(@metric_set_distance_greatest R X A d hD (first z) r)=>a ha.
  have hMember:[set z|A (first z)] (pair a (second z)).
    change (A (first (pair a (second z)))); by rewrite (squared_product_first_pair_law hp).
  have h:=hBound (pair a (second z)) hMember.
  have hDistance:mdist z (pair a (second z))=mdist (first z) a.
    have hh:=@squared_metric_product_first_slice R Z X Y pair first second hp (second z) (first z) a.
    by rewrite (squared_product_recovery_law hp) in hh.
  by rewrite hDistance in h.
Qed.
