(** Federer (1969), 2.4.12, p. 87: continuous real linear functionals have a
    finite norm bound, needed for their integrable evaluations. This
    supporting one-linear version needs no finite-dimensional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ContinuousRealFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_real_functional_bound]: supporting finite bound
    for elements of Y* in Federer 2.4.12, p. 87 The conclusion supplies a
    strictly positive bound, also for the zero functional and
    zero-dimensional spaces, without assuming a chosen norm. *)
Lemma continuous_real_functional_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o}) :
  is_continuous_real_functional hN a -> exists C : R,
    0 < C /\ forall y, `|a y| <= C*N y.
Proof.
move=> ha.
have hball : nbhs (a (0:V) : real_line_metric R) [set z | mdist (a 0 : real_line_metric R) z < 1].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (a 0 : real_line_metric R) _)); exists 1; first exact: ltr01.
  by move=> z hz.
have hpre := ha (0 : real_norm_metric_space hN) _ hball.
have [delta hd hdelta] := proj1 (metricType_numDomainType.nbhs_mdistP (0 : real_norm_metric_space hN) _) hpre.
exists (2/delta); split; first by rewrite divr_gt0 // ltr0n.
move=> y; have [->|hy] := eqVneq y 0.
- by rewrite linear0 normr0 (real_seminorm_zero hN.1) mulr0.
have hny : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
pose t := delta/(2*N y).
have ht : 0 < t by rewrite /t divr_gt0 // mulr_gt0 // ltr0n.
have hty : N (t *: y) = delta/2.
  rewrite (real_seminorm_scale hN.1) (ger0_norm (ltW ht)) /t invfM mulrA.
  by rewrite divfK // gt_eqF.
have hsmall : mdist (0 : real_norm_metric_space hN) (t *: y) < delta.
  change (N (0-t *: y) < delta); rewrite sub0r (real_seminorm_negate hN.1) hty.
  by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have hab := hdelta (t *: y) hsmall.
change (is_true (`|a 0-a (t *: y)| < 1)) in hab.
rewrite linear0 sub0r normrN linearZ /= normrM (ger0_norm (ltW ht)) in hab.
have hb : `|a y| < t^-1 by rewrite -div1r ltr_pdivlMr // mulrC.
apply: ltW; apply: lt_le_trans hb _.
by rewrite /t invf_div mulrAC.
Qed.
