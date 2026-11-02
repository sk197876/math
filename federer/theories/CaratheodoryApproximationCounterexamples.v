(** Federer (1969), 2.10.1, p. 170: "not all open sets" need be measurable
    for an approximating measure; the final measure need not extend the
    assigned costs. These are explicit local examples of the two printed
    observations, not corrections. Use only the single closed interval [0,1]
    as generator, of cost one. No relevant correction in the local Federer
    erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal
  MetricScaleEnvelope MetricScaleEnvelopeUP CaratheodoryLimitUP CaratheodoryMeasure
  CaratheodorySingleGenerator MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [caratheodory_approximation_open_counterexample]:
    explicit example of the open-set failure asserted in Federer
    2.10.1, p. 170. At cutoff one, every nonempty subset
    of the sole generator [0,1] has mass one. The open
    half-line below one half splits that generator into two
    nonempty parts, so it fails the Caratheodory identity. *)
Theorem caratheodory_approximation_open_counterexample (R : realType) :
  let S : set (real_line_metric R) := `[0,1] in
  let nu := metric_scale_envelope (fun _ : unit => S) (fun _ => (1%E : \bar R)) 1%E in
  exists U : set (real_line_metric R), open U /\ ~ measure_measurable nu U.
Proof.
move=> S nu; pose U : set (real_line_metric R) := [set x | x<(1/2 : R)].
have hhalf0 : (0 : R)<1/2 by lra.
have hhalf1 : (1/2 : R)<1 by lra.
have hdiam : (extended_metric_diameter S<=1)%E.
  by rewrite /S (extended_metric_diameter_segment (@ler01 R)) subr0.
have hmass (A : set (real_line_metric R)) : A `<=` S -> (exists x, A x) -> nu A = 1%E.
  exact (@single_generator_scale_mass R [the metricType R of real_line_metric R]
    S A 1%E 1%E ltac:(by []) hdiam).
have hS0 : S 0 by rewrite /S /= in_itv /= lexx ler01.
have hS1 : S 1 by rewrite /S /= in_itv /= lexx ler01.
have hS : nu S = 1%E := hmass S (fun _ h => h) (ex_intro _ 0 hS0).
have hleft : nu (S `&` U) = 1%E.
  apply: hmass; [by move=> x [hx _]|exists 0; by split].
have hright : nu (S `\` U) = 1%E.
  apply: hmass; [by move=> x [hx _]|exists 1; split=> //].
  by rewrite /U /= ltNge (ltW hhalf1).
exists U; split; first exact: open_lt.
move=> hU; have he := hU S; rewrite hS hleft hright in he.
change ((1 : R)%:E=(1+1 : R)%:E) in he.
have he' : (1 : R) = 1+1 by case: he.
by lra.
Qed.

(** Source for [caratheodory_single_interval_not_extension]:
    explicit non-extension example for Federer 2.10.1,
    p. 170. The only generator has cost one and diameter
    one; below that diameter, no nonempty set can be covered.
    Its final mass is infinity, rather than its assigned cost. *)
Theorem caratheodory_single_interval_not_extension (R : realType) :
  let S : set (real_line_metric R) := `[0,1] in
  caratheodory_measure (fun _ : unit => S) (fun _ => (1%E : \bar R)) S=+oo%E.
Proof.
move=> S.
have hdiam : (((1/2 : R))%:E<extended_metric_diameter S)%E.
  rewrite /S (extended_metric_diameter_segment (@ler01 R)) subr0 lte_fin; lra.
have hS0 : S 0 by rewrite /S /= in_itv /= lexx ler01.
have hinf := @single_oversize_generator_scale_mass R [the metricType R of real_line_metric R]
  S S (1/2 : R)%:E 1%E hdiam (ex_intro _ 0 hS0).
have hcut : (0<(1/2 : R)%:E)%E by rewrite lte_fin; lra.
have hb := @caratheodory_limit_upper R [the metricType R of real_line_metric R]
  [the choiceType of (unit : Type)] (fun _ => S) (fun _ => (1%E : \bar R)) _
  (caratheodory_measure_specification (fun _ : unit => S) (fun _ => (1%E : \bar R)))
  S (1/2 : R)%:E _ hcut
  (metric_scale_envelope_specification (fun _ : unit => S) (fun _ => (1%E : \bar R)) (1/2 : R)%:E).
rewrite hinf in hb; by apply/eqP; rewrite eq_le leey hb.
Qed.
