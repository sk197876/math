(** Supporting weighted covering comparison for Federer (1969), 2.10.2, p.
    171: dimensional and spherical comparisons factor a positive finite
    scalar out of all covering costs. This abstract intermediate lemma is
    not separately stated there. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP FiniteMeasureScaling MetricScaleMeasureBound
  MetricScaleEnvelopeUP MetricDiameter NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_generator_bound]: supporting
    one-generator upper bound from the infimum defining
    size-delta approximations, Federer 2.10.1, p. 170,
    used in the comparisons of 2.10.2, p. 171. *)
Lemma metric_scale_generator_bound (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) (j : J) :
  is_metric_scale_envelope S c delta nu -> 0<=c j ->
  extended_metric_diameter (S j)<=delta -> nu (S j)<=c j.
Proof.
move=> hn hc hd.
have hcov : S j `<=` \bigcup_(k in [set j]) S k by move=> x hx; exists j.
have hsize k : [set j] k -> extended_metric_diameter (S k)<=delta by move=> ->.
have hh := @metric_scale_envelope_lower R X J S c delta nu hn (S j)
  [set j] (countable1 j) hsize hcov.
by rewrite nonnegative_sum_singleton in hh.
Qed.

(** Source for [measure_bounded_by_scaled_metric_envelope]:
    supporting extraction of the positive finite factor in
    Federer 2.10.2, p. 171. Scale the competing measure
    by its reciprocal, apply the unweighted covering law,
    then multiply back; infinite values require no division. *)
Theorem measure_bounded_by_scaled_metric_envelope (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (delta : \bar R) (nu mu : set X -> \bar R) (a : R) :
  is_metric_scale_envelope S c delta nu -> is_measure mu -> (0<a)%R ->
  (forall j, extended_metric_diameter (S j)<=delta -> mu (S j)<=a%:E*c j) ->
  forall A, mu A<=a%:E*nu A.
Proof.
move=> hn hm ha hj A.
have hai : (0<=a^-1)%R by rewrite invr_ge0; exact: ltW ha.
have haiE : 0<=((a^-1)%R)%:E by rewrite lee_fin.
have haE : 0<=a%:E by rewrite lee_fin; exact: ltW ha.
have hscaled : is_measure (fun B => ((a^-1)%R)%:E*mu B) := finite_scale_is_measure hm hai.
have hgen j : extended_metric_diameter (S j)<=delta -> ((a^-1)%R)%:E*mu (S j)<=c j.
  move=> hd; have hh := lee_wpmul2l haiE (hj j hd).
  by rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in hh.
have hb := @measure_bounded_by_metric_scale_envelope R X J S c delta nu
  (fun B => ((a^-1)%R)%:E*mu B) hn hscaled hgen A.
have hh := lee_wpmul2l haE hb.
by rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in hh.
Qed.
