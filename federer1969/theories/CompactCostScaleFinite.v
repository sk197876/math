(** Federer (1969), 2.10.22, p. 184: the fixed-cutoff mass of a bounded
    compact ball is finite. Expand the printed compactness observation by a
    finite cover with small compact balls. This supporting statement allows
    any compact target and needs only finite nonnegative generator costs. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile MetricClosedBalls MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleIndexedCover NonnegativeSum CompactFiniteCover LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_generator_scale_finite]: supporting
    finiteness assertion in 2.10.22, p. 184:
    every compact target has finite mass at every
    finite strictly positive cutoff. *)
Theorem compact_generator_scale_finite (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) (delta : R) (nu : set X -> \bar R) (K : set X) :
  metric_boundedly_compact X -> (forall C, 0<=cost C) -> 0<delta ->
  is_metric_scale_envelope (fun C : compact_metric_set X => val C) (fun C => (cost C)%:E) delta%:E nu ->
  compact K -> (nu K < +oo)%E.
Proof.
move=> hX hc hd hn hK.
pose r := delta/4.
have hr : 0<r by rewrite /r divr_gt0 // ltr0n.
have hball x : compact (metric_closed_ball x r) := hX x r (ltW hr).
have hne (x : X) : metric_closed_ball x r !=set0.
  exists x; rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
pose B (x : X) : compact_metric_set X := exist _ (metric_closed_ball x r) (mem_set (conj (hball x) (hne x))).
have hdiam x : (extended_metric_diameter (val (B x))<=delta%:E)%E.
  apply: (@metric_diameter_least R X (val (B x)) (extended_metric_diameter (val (B x)))
    (extended_metric_diameter_specification (val (B x))) delta%:E).
  - rewrite lee_fin; exact: ltW hd.
  - move=> y z hy hz; rewrite lee_fin.
    have hh := metric_closed_ball_diameter_bound hy hz; rewrite /r in hh; lra.
have hcover : K `<=` \bigcup_(x in [set: X]) [set y | mdist x y<r].
  move=> x hx; exists x=> //; by rewrite /= mdistxx.
have [F hF hcov] := @compact_open_finite_cover X X setT (fun x => [set y | mdist x y<r]) K
  hK (fun x _ => metric_open_ball_open x r) hcover.
have hclosedcover : K `<=` \bigcup_(x in [set` F]) val (B x).
  move=> y hy; have [x hx hxy] := hcov y hy; exists x=> //; exact: ltW hxy.
have hc0 x : (0<=(cost (B x))%:E)%E by rewrite lee_fin; exact: hc.
have hh := @metric_scale_envelope_indexed_cover R X (compact_metric_set X) X
  (fun C=>val C) (fun C=>(cost C)%:E) delta%:E nu hn K [set` F] B
  (finite_set_countable (finite_fset F)) (fun x _=>hc0 x) (fun x _=>hdiam x) hclosedcover.
have hs : (nonnegative_sum [set` F] (fun x=>(cost (B x))%:E)< +oo)%E.
  rewrite nonnegative_sum_finite; last by move=> x hx; exact: hc0.
  rewrite sumEFin; exact: ltry.
exact: le_lt_trans hh hs.
Qed.
