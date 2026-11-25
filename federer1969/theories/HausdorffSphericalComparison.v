(** Federer (1969), 2.10.2(2), p. 171, last display: H^m <= S^m <= 2^m H^m.
    Here the radius is enlarged positively before taking the infimum, so the
    proof retains Federer's strictly positive radii (2.8.1, p. 141), even
    for singleton generators of diameter zero. No radius-zero ball or
    identity between radius and diameter is assumed. Integer degrees are
    treated, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  HausdorffDiameterCost HausdorffPowerCostLaws HausdorffGaugeContinuity
  MetricClosedBalls MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleMeasureBound
  CaratheodoryLimitUP CaratheodoryBorelRegular CaratheodoryTransport
  MeasureUP FiniteMeasureScaling NonnegativeSum NonnegativeSumSupport ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_generator_forget]: supporting
    inclusion of closed-ball generators into all nonempty
    subsets in Federer 2.10.2(2), p. 171. *)
Definition spherical_generator_forget (R : realType) (X : metricType R)
    (j : @positive_closed_metric_balls R X) : @nonempty_metric_sets R X :=
  @exist _ (fun A : set X => A \in [set A | A !=set0]) (val j)
    (mem_set (positive_metric_closed_ball_nonempty (set_valP j))).

(** Source for [hausdorff_measure_le_spherical_measure]: direct first
    inequality of Federer 2.10.2(2), p. 171 Restricting the admissible
    covering family increases the infimum. *)
Theorem hausdorff_measure_le_spherical_measure (R : realType) (X : metricType R)
    (m : nat) (A : set X) :
  @hausdorff_measure R X m A<=@spherical_measure R X m A.
Proof.
have hh := @caratheodory_limit_transport R X X
  (@positive_closed_metric_balls R X) (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => val j)
  (fun j => hausdorff_diameter_cost m (val j))
  (fun j => hausdorff_diameter_cost m (val j)) id (@spherical_generator_forget R X)
  (@spherical_measure R X m) (@hausdorff_measure R X m)
  (@spherical_measure_specification R X m) (@hausdorff_measure_specification R X m).
have hb : @hausdorff_measure R X m (id @` A)<=@spherical_measure R X m A.
  apply: hh.
  - move=> j; exact: hausdorff_diameter_cost_nonnegative.
  - by move=> j x hx.
  - by move=> j.
  - by move=> j.
by rewrite image_id in hb.
Qed.

(** Source for [hausdorff_power_cost_double]: supporting factor 2^m in
    Federer 2.10.2(2), p. 171 Finite real diameters suffice after choosing a
    finite cutoff. *)
Lemma hausdorff_power_cost_double (R : realType) (m : nat) (d : R) :
  hausdorff_power_cost m (d+d)%R%:E=((2:R)^+m)%:E*hausdorff_power_cost m d%:E.
Proof.
rewrite !hausdorff_power_cost_finite -EFinM.
have hd : (d+d = 2*d)%R by lra.
have he : ((d+d)^+m=(2:R)^+m*d^+m)%R by rewrite hd exprMn.
by rewrite he mulrCA mulrA.
Qed.

(** Source for [spherical_scale_generator_bound]: supporting centered-ball
    comparison in Federer 2.10.2(2), p. 171 Infima of strictly positive
    enlarged radii handle zero-diameter generators uniformly, without
    inserting radius-zero balls. *)
Lemma spherical_scale_generator_bound (R : realType) (X : metricType R)
    (m : nat) (nu : set X -> \bar R) (A : set X) (d t : R) :
  is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) t%:E nu ->
  A !=set0 -> (0<=d)%R -> (d+d<t)%R -> extended_metric_diameter A<=d%:E ->
  nu A<=hausdorff_power_cost m (d+d)%R%:E.
Proof.
move=> hn [a ha] hd hdt hdiam; rewrite hausdorff_power_cost_finite.
rewrite leNgt; apply/negP=> hbad.
have [q [hq hqn]] := @extended_rationals_order_dense R
  (hausdorff_normalisation R m*(d+d)^+m)%:E (nu A) hbad.
have hb : (hausdorff_normalisation R m*(d+d)^+m<ratr q)%R by move: hq; rewrite lte_fin.
have [r [hr [hcap hcost]]] := @hausdorff_real_gauge_small_enlargement R m (d+d) t (ratr q) hdt hb.
have hdr : (0<d+r)%R by lra.
pose B := metric_closed_ball a (d+r)%R.
pose j : @positive_closed_metric_balls R X :=
  @exist _ (fun C : set X => C \in [set C | @is_positive_metric_closed_ball R X C]) B
    (mem_set (positive_closed_ball_satisfies_laws a hdr)).
have hAB : A `<=` B.
  move=> x hx; change (is_true (mdist a x<=d+r)%R).
  have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification A) ha hx) hdiam.
  have hax : (mdist a x<=d)%R by move: hh; rewrite lee_fin.
  lra.
have hBdiam : extended_metric_diameter B<=(d+d+r+r)%R%:E.
  apply: (metric_diameter_least (extended_metric_diameter_specification B)).
  - rewrite lee_fin; lra.
  - move=> x y hx hy; rewrite lee_fin.
    have hh := metric_closed_ball_diameter_bound hx hy; lra.
have hsize k : [set j] k -> extended_metric_diameter (val k)<=t%:E.
  move=> ->; apply: le_trans hBdiam _; rewrite lee_fin; exact: ltW hcap.
have hcov : A `<=` \bigcup_(k in [set j]) val k.
  move=> x hx; exists j=> //; exact: hAB x hx.
have hbound := @metric_scale_envelope_lower R X (@positive_closed_metric_balls R X)
  (fun k => val k) (fun k => hausdorff_diameter_cost m (val k)) t%:E nu hn
  A [set j] (countable1 j) hsize hcov.
rewrite nonnegative_sum_singleton in hbound; last exact: hausdorff_diameter_cost_nonnegative.
have hcostB : hausdorff_diameter_cost m B<=(hausdorff_normalisation R m*(d+d+r+r)^+m)%:E.
  rewrite /hausdorff_diameter_cost -hausdorff_power_cost_finite.
  exact (@hausdorff_power_cost_monotone R m _ _
    (metric_diameter_nonnegative (extended_metric_diameter_specification B)) hBdiam).
have hlt : nu A<(ratr q : R)%:E.
  apply: le_lt_trans (le_trans hbound hcostB) _; by rewrite lte_fin.
by have := lt_trans hqn hlt; rewrite ltxx.
Qed.

(** Source for [spherical_measure_le_double_hausdorff_measure]: direct
    second inequality of Federer 2.10.2(2), p. 171 Strictly positive
    enlarged balls are used before taking the infimum, including at degree
    zero and diameter zero. *)
Theorem spherical_measure_le_double_hausdorff_measure (R : realType) (X : metricType R)
    (m : nat) (A : set X) :
  @spherical_measure R X m A<=((2:R)^+m)%:E*@hausdorff_measure R X m A.
Proof.
have hm := @hausdorff_measure_specification R X m.
have hn := @spherical_measure_specification R X m.
pose c : R := ((2:R)^+m)%R.
have hc : (0<c)%R by rewrite /c exprn_gt0 // ltr0n.
have hci : (0<=c^-1)%R by rewrite invr_ge0; exact: ltW hc.
have hcE : 0<=c%:E by rewrite lee_fin; exact: ltW hc.
have hciE : 0<=((c^-1)%R)%:E by rewrite lee_fin.
apply: (caratheodory_limit_least hn)=> tau xi htau hxi.
have [n hnt] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((n.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
pose psi := metric_scale_envelope (fun j : @positive_closed_metric_balls R X => val j)
  (fun j => hausdorff_diameter_cost m (val j)) t%:E.
have hpsi := @metric_scale_envelope_specification R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) t%:E.
have hpsi_measure : is_measure psi := @metric_scale_envelope_measure R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) t%:E
  (fun j => hausdorff_diameter_cost_nonnegative m (val j)).
pose phi := metric_scale_envelope (fun j : @nonempty_metric_sets R X => val j)
  (fun j => hausdorff_diameter_cost m (val j)) ((t/4)%R%:E).
have hphi := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) ((t/4)%R%:E).
have hgen (j : @nonempty_metric_sets R X) : extended_metric_diameter (val j)<=(t/4)%R%:E ->
    ((c^-1)%R)%:E*psi (val j)<=hausdorff_diameter_cost m (val j).
  move=> hj; have h0 := metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  case he: (extended_metric_diameter (val j)) h0 hj=> [d| |] h0 hj; last 2 first.
  + by rewrite leye_eq in hj.
  + by [].
  have hd : (0<=d)%R by move: h0; rewrite lee_fin.
  have hdt : (d+d<t)%R.
    have hh : (d<=t/4)%R by move: hj; rewrite lee_fin.
    have h4 : (0<(4:R))%R by rewrite ltr0n.
    have htt : (t/4+t/4<t)%R.
      have hq : (t/4*4=t)%R by rewrite divfK ?pnatr_eq0.
      lra.
    lra.
  have hdi : extended_metric_diameter (val j)<=d%:E by rewrite he.
  have hb := @spherical_scale_generator_bound R X m psi (val j) d t hpsi (set_valP j) hd hdt hdi.
  rewrite hausdorff_power_cost_double in hb.
  have hh := lee_wpmul2l hciE hb.
  rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in hh.
  by rewrite /hausdorff_diameter_cost he.
have hb := @measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) ((t/4)%R%:E)
  phi (fun B => ((c^-1)%R)%:E*psi B) hphi (finite_scale_is_measure hpsi_measure hci) hgen A.
have hup : phi A<=@hausdorff_measure R X m A.
  apply: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) _ hm A ((t/4)%R%:E) phi _ hphi).
  by rewrite lte_fin divr_gt0 // ltr0n.
have hh := lee_wpmul2l hcE (le_trans hb hup).
rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in hh.
apply: le_trans _ hh.
exact (@metric_scale_envelope_antitone_cutoff R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) t%:E tau psi xi hpsi hxi hnt A).
Qed.
