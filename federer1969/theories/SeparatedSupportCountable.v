(** Federer (1969), 2.2.16, p. 71: disjoint positive-measure balls centred
    in a separated support subset make that subset countable, by 2.1.6(2),
    p. 59. No separability of the ambient space is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDisjointSupport
  MeasureSupportUP MeasureSupportLaws MeasureSupport MetricClosedBalls SeparatedMetricSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [separated_metric_open_balls_disjoint]: supporting
    ball argument in Federer 2.2.16, p. 71.
    Centres at distance greater than r+r have disjoint open
    radius-r balls, by the triangle inequality. *)
Lemma separated_metric_open_balls_disjoint (R : realType) (X : metricType R)
    (S : set X) (r : R) : is_strictly_separated_metric_set (r+r)%R S ->
  forall x y, S x -> S y -> x <> y ->
    [set z | (mdist x z < r)%R] `&` [set z | (mdist y z < r)%R] = set0.
Proof.
move=> hs x y hx hy hxy; apply/seteqP; split; last by move=> z [].
move=> z [hxz hyz].
have ht := metric_triangle x z y; rewrite (metric_sym z y) in ht.
have hl := le_lt_trans ht (ltrD hxz hyz).
have hh := lt_trans (hs x y hx hy hxy) hl; by move: hh; rewrite ltxx.
Qed.

(** Source for [separated_support_set_countable]: direct
    countability of A_n in Federer 2.2.16, p. 71,
    with a general positive radius r replacing 1/n. Finiteness
    of the whole measure and measurability of opens are retained. *)
Theorem separated_support_set_countable (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (S : set X) (r : R) :
  mu setT < +oo -> (forall U, open U -> measure_measurable mu U) ->
  (0 < r)%R -> S `<=` measure_support mu ->
  is_strictly_separated_metric_set (r+r)%R S -> countable S.
Proof.
move=> hf ho hr hS hs.
pose B (x : X) := [set z | (mdist x z < r)%R].
have hp x : S x -> 0 < mu (B x).
  move=> hx.
  have h := proj1 (@measure_support_positive_neighborhood R X mu hm _
    (measure_support_specification mu) x) (hS x hx).
  apply: h; first exact: metric_open_ball_open.
  by rewrite /B /= mdistxx.
have hsub x : S x -> B x `<=` setT by move=> hx z hz.
have hmeas x : S x -> measure_measurable mu (B x).
  move=> hx; apply: ho; exact: metric_open_ball_open.
have hd x y : S x -> S y -> x <> y -> B x `&` B y = set0.
  exact: (@separated_metric_open_balls_disjoint R X S r hs x y).
have hc := @measure_disjoint_positive_countable R X X mu hm setT S B hf hsub hmeas hd.
have he : S `&` [set x | 0 < mu (B x)] = S.
  apply/seteqP; split; first by move=> x [hx _].
  move=> x hx; split=> //; exact: hp hx.
by rewrite he in hc.
Qed.
