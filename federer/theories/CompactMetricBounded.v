(** Federer (1969), 2.10.21, p. 183: compact sets have finite diameter and
    lie in a closed ball about any prescribed centre. These supporting
    topology facts justify the real-valued diameter map and extending
    finite-set density beyond F_(a,r). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricClosedBalls CompactSetDistanceProfile
  NormMetricScaleContinuity CompactMaximum MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_set_ball_bound]: supporting
    finite radius for a compact set in 2.10.21,
    p. 183. The centre is arbitrary and the
    radius is made positive without changing the set. *)
Lemma compact_metric_set_ball_bound (R : realType) (X : metricType R)
    (C : compact_metric_set X) (a : X) :
  exists r : R, 0<r /\ val C `<=` metric_closed_ball a r.
Proof.
have hf : continuous (fun x : X => (mdist a x : real_line_metric R)).
  apply: (@metric_fixed_lipschitz_continuous R X [the metricType R of real_line_metric R] _ 1 (@ler01 R))=> x y.
  rewrite real_line_metric_distanceE mul1r ler_norml; apply/andP; split.
  - have hh := metric_triangle a x y; lra.
  - have hh := metric_triangle a y x; rewrite (metric_sym y x) in hh; lra.
have [c [hc hmax]] := continuous_compact_maximum (set_valP C).2 (set_valP C).1 hf.
exists (mdist a c+1); split.
- have hh := mdist_ge0 a c; lra.
- move=> x hx; apply: le_trans (hmax x hx) _; lra.
Qed.

(** Source for [compact_metric_diameter_finite]: supporting
    finiteness of the diameter in 2.10.21,
    p. 183. Use the already sealed extended
    diameter and its pairwise least-upper-bound laws. *)
Lemma compact_metric_diameter_finite (R : realType) (X : metricType R)
    (C : compact_metric_set X) : (extended_metric_diameter (val C) < +oo)%E.
Proof.
have [a ha] := (set_valP C).2.
have [r [hr hball]] := compact_metric_set_ball_bound C a.
have hb : (extended_metric_diameter (val C)<=(r+r)%:E)%E.
  apply: (@metric_diameter_least R X (val C) (extended_metric_diameter (val C))
    (extended_metric_diameter_specification (val C)) (r+r)%:E).
  - by rewrite lee_fin; exact: addr_ge0 (ltW hr) (ltW hr).
  - move=> x y hx hy; rewrite lee_fin.
    exact: metric_closed_ball_diameter_bound (hball x hx) (hball y hy).
exact: le_lt_trans hb (ltry _).
Qed.

(** Source for [compact_metric_diameter]: direct real-valued
    diameter map in 2.10.21, p. 183. The
    preceding finiteness proof justifies taking its finite part. *)
Definition compact_metric_diameter (R : realType) (X : metricType R) (C : compact_metric_set X) :=
  fine (extended_metric_diameter (val C)).

(** Source for [compact_metric_diameter_finite_value]: supporting
    compatibility with the actual diameter in
    2.10.21, p. 183; no default value at
    infinity is used on a compact set. *)
Lemma compact_metric_diameter_finite_value (R : realType) (X : metricType R) (C : compact_metric_set X) :
  extended_metric_diameter (val C)=(compact_metric_diameter C)%:E.
Proof.
have h0 := metric_diameter_nonnegative (extended_metric_diameter_specification (val C)).
have hfin : extended_metric_diameter (val C) \is a fin_num.
  by rewrite (ge0_fin_numE h0); exact: compact_metric_diameter_finite.
by rewrite /compact_metric_diameter fineK.
Qed.
