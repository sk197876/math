(** Federer (1969), 2.10.27, pp. 190–191: supporting normalized Lebesgue
    volume of closed Euclidean balls in the section calculation. The
    open-ball formula is 2.7.16, p. 135. Prove the closed-ball formula by
    arbitrarily small open enlargements and the existing polynomial-gauge
    continuity, retaining radius zero and dimension zero. No equality
    between open and closed balls is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanLebesgueDimensions EuclideanBallVolume
  HausdorffDiameterCost HausdorffRadiusCost HausdorffGaugeContinuity ExtendedRealOrderTopology MetricClosedBalls MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_closed_ball_volume_upper]: supporting
    closed-ball upper volume bound in 2.10.27,
    p. 191. A slightly larger open ball has
    polynomial cost below any strict proposed upper
    budget. Radius zero and all natural dimensions
    are retained. *)
Lemma euclidean_closed_ball_volume_upper (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  (0<=r)%R -> @euclidean_lebesgue_measure R n (metric_closed_ball a r)<=
    (euclidean_unit_ball_volume R n*r^+n)%R%:E.
Proof.
move=> hr; rewrite leNgt; apply/negP=> hbad.
have [q [hbq hqm]] := @extended_rationals_order_dense R
  (euclidean_unit_ball_volume R n*r^+n)%R%:E
  (@euclidean_lebesgue_measure R n (metric_closed_ball a r)) hbad.
have hb : (hausdorff_normalisation R n*(r+r)^+n<ratr q)%R.
  rewrite hausdorff_doubled_radius_normalisation; exact hbq.
have hcap : (r+r<r+r+1)%R by rewrite ltrDl ltr01.
have [e [he [_ hcost]]] := @hausdorff_real_gauge_small_enlargement R n
  (r+r)%R (r+r+1)%R (ratr q) hcap hb.
have hpos : (0<r+e)%R by lra.
have hsum : (r+r+e+e=(r+e)+(r+e))%R by lra.
rewrite hsum hausdorff_doubled_radius_normalisation in hcost.
have hsub : metric_closed_ball a r `<=` [set x : inner_metric_space (@euclidean_inner_productP R n) | (`|x-a|<r+e)%R].
  move=> x hx; have hx' : (`|x-a|<=r)%R by rewrite -inner_metric_normE; exact hx.
  apply: le_lt_trans hx' _; by rewrite ltrDl.
have hh := @measure_mono R _ (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ hsub.
rewrite (@euclidean_ball_measure R n a (r+e)%R hpos) in hh.
have hcostE : (euclidean_unit_ball_volume R n*(r+e)^+n)%R%:E<(ratr q : R)%:E.
  by rewrite lte_fin.
have hbad' := lt_trans hqm (le_lt_trans hh hcostE); by rewrite ltxx in hbad'.
Qed.

(** Source for [euclidean_closed_ball_normalized_volume]: supporting
    closed-ball volume used in 2.10.27, p. 191.
    Includes zero radius. In dimension zero every
    nonnegative-radius ball has unit mass, so 0^0=1
    agrees with the existing empty-product convention. *)
Theorem euclidean_closed_ball_normalized_volume (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  (0<=r)%R -> @euclidean_lebesgue_measure R n (metric_closed_ball a r)=
    (euclidean_unit_ball_volume R n*r^+n)%R%:E.
Proof.
move=> hr; apply/eqP; rewrite eq_le (euclidean_closed_ball_volume_upper a hr) /=.
case: (ltP 0%R r)=> [hpos|hnon].
- rewrite -(@euclidean_ball_measure R n a r hpos).
  apply: (@measure_mono R _ (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)).
  move=> x hx; rewrite /metric_closed_ball /= inner_metric_normE; exact: ltW hx.
- have hz : r=0%R by apply/eqP; rewrite eq_le hnon hr.
  rewrite hz; case: n a=> [a|n a]; last first.
    rewrite exprS mul0r mulr0.
    exact: (@measure_nonnegative R _ (@euclidean_lebesgue_measure R n.+1)
      (euclidean_lebesgue_is_measure R n.+1) (metric_closed_ball a 0%R)).
  rewrite expr0 mulr1.
  have hsub : [set x : inner_metric_space (@euclidean_inner_productP R 0) | (`|x-a|<1)%R] `<=`
      metric_closed_ball a 0%R.
    move=> x _; have hx : x=a by rewrite (@coordinate_zero R x) (@coordinate_zero R a).
    by rewrite hx /metric_closed_ball /= mdistxx.
  have hh := @measure_mono R _ (@euclidean_lebesgue_measure R 0)
    (euclidean_lebesgue_is_measure R 0) _ _ hsub.
  by rewrite (@euclidean_ball_measure R 0 a 1%R ltr01) expr1n mulr1 in hh.
Qed.
