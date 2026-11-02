(** Federer (1969), 2.10.29, p. 195: finite Cartesian powers of one Cantor
    set are covered by same-level coordinate interval boxes. A box of side
    lengths at most r in R^q has diameter at most q*r. This weaker bound
    than sqrt(q)*r suffices for the printed finiteness assertion, which
    specifies no sharp constant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanLebesgueHaar RealMetricBackground CompactIntervalGauge CompactIntervalDiameter
  MetricDiameterUP MetricDiameter MetricDiameterReal HausdorffLengthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Boxes.
Variable R : realType.
Variable q : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R q)).

(** Source for [euclidean_interval_box]: supporting
    actual coordinate interval box in R^q
    for the finite Cartesian-power covers in
    2.10.29, p. 195. Coordinate membership
    specifies the set, without endpoint choices. *)
Definition euclidean_interval_box (F : 'I_q -> compact_real_intervals R) : set E :=
  [set x | forall i, val (F i) (x i)].

(** Source for [euclidean_interval_box_nonempty]: supporting
    nonempty cover generators for 2.10.29,
    p. 195. Coordinates are chosen only
    inside this existence proof. The empty
    coordinate family is also included. *)
Lemma euclidean_interval_box_nonempty (F : 'I_q -> compact_real_intervals R) :
  euclidean_interval_box F !=set0.
Proof.
have hex i : exists x : R, val (F i) x := compact_real_interval_nonempty (set_valP (F i)).
pose a i := projT1 (cid (hex i)).
exists ([ffun i=>a i] : E)=> i; rewrite ffunE; exact: projT2 (cid (hex i)).
Qed.

(** Source for [euclidean_interval_box_generator]: supporting
    inclusion of actual coordinate boxes in
    the nonempty covering family of 2.10.29,
    p. 195. The underlying predicate and
    nonemptiness law have already been proved. *)
Definition euclidean_interval_box_generator (F : 'I_q -> compact_real_intervals R) :
    @nonempty_metric_sets R [the metricType R of E] :=
  Sub (euclidean_interval_box F) (mem_set (euclidean_interval_box_nonempty F)).

(** Source for [euclidean_interval_box_diameter_bound]: supporting
    q*r diameter bound for the finite-power
    covers in 2.10.29, p. 195. It
    follows from the coordinate norm sum
    and includes zero width and q=0. *)
Lemma euclidean_interval_box_diameter_bound (F : 'I_q -> compact_real_intervals R) (r : R) :
  0<=r ->
  (forall i, fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val (F i)))<=r) ->
  (@extended_metric_diameter R [the metricType R of E] (euclidean_interval_box F)<=(q%:R*r)%:E)%E.
Proof.
move=> hr hF.
apply: (metric_diameter_least (extended_metric_diameter_specification (euclidean_interval_box F))).
- rewrite lee_fin; exact (mulr_ge0 (@ler0n R q) hr).
- move=> x y hx hy; rewrite lee_fin inner_metric_normE.
  apply: le_trans (@euclidean_norm_coordinate_sum R q (y-x)) _.
  have hcoords i : `|(y-x) i|<=r.
    rewrite !ffunE.
    have hh := metric_diameter_upper (extended_metric_diameter_specification (val (F i))) (hy i) (hx i).
    rewrite real_line_metric_distanceE (compact_interval_diameter_finite_value (set_valP (F i))) lee_fin in hh.
    exact (le_trans hh (hF i)).
  have hh : \sum_i `|(y-x) i|<=\sum_(i : 'I_q) r.
    apply: ler_sum=> i _; exact: hcoords.
  by rewrite sumr_const card_ord -mulr_natl in hh.
Qed.
End Boxes.
