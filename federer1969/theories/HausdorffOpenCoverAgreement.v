(** Federer (1969), 2.10.2(1), p. 171: the final Hausdorff measure is
    unchanged by restricting generators to nonempty open sets. Preliminary
    cutoffs are compared with a strictly smaller cutoff; equality at each
    fixed cutoff is neither assumed nor asserted. The proof below treats the
    printed integer degrees. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  HausdorffDiameterCost HausdorffPowerCostLaws HausdorffGaugeContinuity
  MetricOpenThickening MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  MetricScaleEnvelope MetricScaleMeasureBound MetricScaleEnvelopeLaws
  CaratheodoryLimitUP CaratheodoryBorelRegular CaratheodoryTransport
  MeasureUP NonnegativeSum NonnegativeSumSupport ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_hausdorff_scale_generator_bound]:
    supporting enlargement step for Federer 2.10.2(1),
    p. 171. When the diameter bound d is strictly below
    the open-cover cutoff, positive open thickenings have
    costs arbitrarily close to the original polynomial gauge. *)
Lemma open_hausdorff_scale_generator_bound (R : realType) (X : metricType R)
    (m : nat) (nu : set X -> \bar R) (A : set X) (d t : R) :
  is_metric_scale_envelope (fun j : @nonempty_open_metric_sets R X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) t%:E nu ->
  A !=set0 -> (0<=d)%R -> (d<t)%R -> extended_metric_diameter A<=d%:E ->
  nu A<=hausdorff_power_cost m d%:E.
Proof.
move=> hn hA hd hdt hdiam; rewrite hausdorff_power_cost_finite.
rewrite leNgt; apply/negP=> hbad.
have [q [hq hqn]] := @extended_rationals_order_dense R
  (hausdorff_normalisation R m*d^+m)%:E (nu A) hbad.
have hb : (hausdorff_normalisation R m*d^+m<ratr q)%R by move: hq; rewrite lte_fin.
have [r [hr [hcap hcost]]] := @hausdorff_real_gauge_small_enlargement R m d t (ratr q) hdt hb.
pose U := metric_open_thickening A r.
have hAU : A `<=` U := metric_open_thickening_includes hr.
have hUne : U !=set0 by have [x hx] := hA; exists x; exact: hAU x hx.
pose j : @nonempty_open_metric_sets R X :=
  @exist _ (fun B : set X => B \in [set B | open B /\ B !=set0]) U
    (mem_set (conj (metric_open_thickening_open A r) hUne)).
have hUdiam : extended_metric_diameter U<=(d+r+r)%R%:E :=
  metric_open_thickening_diameter_bound hd (ltW hr) hdiam.
have hsize k : [set j] k -> extended_metric_diameter (val k)<=t%:E.
  move=> ->; apply: le_trans hUdiam _; rewrite lee_fin; exact: ltW hcap.
have hcov : A `<=` \bigcup_(k in [set j]) val k.
  move=> x hx; exists j=> //; exact: hAU x hx.
have hbound := @metric_scale_envelope_lower R X (@nonempty_open_metric_sets R X)
  (fun k => val k) (fun k => hausdorff_diameter_cost m (val k)) t%:E nu hn
  A [set j] (countable1 j) hsize hcov.
rewrite nonnegative_sum_singleton in hbound; last exact: hausdorff_diameter_cost_nonnegative.
have hcostU : hausdorff_diameter_cost m U<=(hausdorff_normalisation R m*(d+r+r)^+m)%:E.
  rewrite /hausdorff_diameter_cost -hausdorff_power_cost_finite.
  exact (@hausdorff_power_cost_monotone R m _ _
    (metric_diameter_nonnegative (extended_metric_diameter_specification U)) hUdiam).
have hlt : nu A<(ratr q : R)%:E.
  apply: le_lt_trans (le_trans hbound hcostU) _; by rewrite lte_fin.
by have := lt_trans hqn hlt; rewrite ltxx.
Qed.

(** Source for [nonempty_open_forget]: supporting inclusion
    of the open generator family in all nonempty subsets
    for Federer 2.10.2(1), p. 171. *)
Definition nonempty_open_forget (R : realType) (X : metricType R)
    (j : @nonempty_open_metric_sets R X) : @nonempty_metric_sets R X :=
  @exist _ (fun A : set X => A \in [set A | A !=set0]) (val j) (mem_set (set_valP j).2).

(** Source for [hausdorff_open_cover_agreement]: direct
    final-measure equality with open covers in Federer
    2.10.2(1), p. 171. Finite cutoffs suffice by
    cofinality; one first compares the cutoff t to t/2. *)
Theorem hausdorff_open_cover_agreement (R : realType) (X : metricType R)
    (m : nat) (mu nu : set X -> \bar R) :
  is_hausdorff_measure m mu -> is_open_hausdorff_measure m nu -> forall A, mu A=nu A.
Proof.
move=> hm hn A.
have hle : mu (id @` A)<=nu A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_open_metric_sets R X) (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => val j)
    (fun j => hausdorff_diameter_cost m (val j))
    (fun j => hausdorff_diameter_cost m (val j)) id (@nonempty_open_forget R X)
    nu mu hn hm _ _ _ _ A).
  - move=> j; exact: hausdorff_diameter_cost_nonnegative.
  - by move=> j x hx.
  - by move=> j.
  - by move=> j.
rewrite image_id in hle.
apply/eqP; rewrite eq_le hle /=.
apply: (caratheodory_limit_least hn)=> tau xi htau hxi.
have [n hnt] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((n.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
pose psi := metric_scale_envelope (fun j : @nonempty_open_metric_sets R X => val j)
  (fun j => hausdorff_diameter_cost m (val j)) t%:E.
have hpsi := @metric_scale_envelope_specification R X (@nonempty_open_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) t%:E.
apply: le_trans (@metric_scale_envelope_antitone_cutoff R X (@nonempty_open_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) t%:E tau psi xi hpsi hxi hnt A) _.
pose phi := metric_scale_envelope (fun j : @nonempty_metric_sets R X => val j)
  (fun j => hausdorff_diameter_cost m (val j)) ((t/2)%R%:E).
have hphi := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) ((t/2)%R%:E).
have hpsi_measure : is_measure psi := @metric_scale_envelope_measure R X (@nonempty_open_metric_sets R X)
  (fun j : @nonempty_open_metric_sets R X => val j)
  (fun j => hausdorff_diameter_cost m (val j)) t%:E
  (fun j => hausdorff_diameter_cost_nonnegative m (val j)).
have hgen (j : @nonempty_metric_sets R X) : extended_metric_diameter (val j)<=(t/2)%R%:E ->
    psi (val j)<=hausdorff_diameter_cost m (val j).
  move=> hj; have h0 := metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  case he: (extended_metric_diameter (val j)) h0 hj=> [d| |] h0 hj; last 2 first.
  + by rewrite leye_eq in hj.
  + by [].
  have hd : (0<=d)%R by move: h0; rewrite lee_fin.
  have hdt : (d<t)%R.
    have hh : (d<=t/2)%R by move: hj; rewrite lee_fin.
    have h2 : (0<(2:R))%R by rewrite ltr0n.
    have htt : (t/2<t)%R by rewrite (ltr_pdivrMr _ _ h2); lra.
    exact: le_lt_trans hh htt.
  rewrite /hausdorff_diameter_cost he.
  have hdi : extended_metric_diameter (val j)<=d%:E by rewrite he.
  exact (@open_hausdorff_scale_generator_bound R X m psi (val j) d t hpsi
    (set_valP j) hd hdt hdi).
apply: le_trans (@measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) ((t/2)%R%:E)
  phi psi hphi hpsi_measure hgen A) _.
apply: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) mu hm A ((t/2)%R%:E) phi _ hphi).
by rewrite lte_fin divr_gt0 // ltr0n.
Qed.

(** Source for [hausdorff_open_measure_equality]: public
    open-cover equality of Federer 2.10.2(1), p. 171,
    between the independently sealed selected measures. *)
Theorem hausdorff_open_measure_equality (R : realType) (X : metricType R)
    (m : nat) (A : set X) :
  @hausdorff_measure R X m A=@open_hausdorff_measure R X m A.
Proof. exact (@hausdorff_open_cover_agreement R X m _ _
  (@hausdorff_measure_specification R X m) (@open_hausdorff_measure_specification R X m) A). Qed.
