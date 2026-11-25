(** Federer (1969), 3.1.8, pp. 217–218: the
    common point outside two growth-exception sets gives a
    Lipschitz bound between sufficiently close cutoff points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  ApproximateMetricGrowth EuclideanGrowthCutoffs EuclideanOverlapGoodPoint LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_growth_cutoff_pair_bound]:
    the bound |f(u)-f(v)|<=2j|u-v| for nearby points
    of B_j, Federer 3.1.8, pp. 217–218.
    The common point is found from actual outer-measure bounds. *)
Lemma euclidean_growth_cutoff_pair_bound (R : realType) m
    (Y : metricType R)
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->Y) j u v :
  euclidean_growth_cutoff A f j u ->
  euclidean_growth_cutoff A f j v ->
  mdist u v<(j.+1%:R : R)^-1 ->
  mdist (f u) (f v)<=2*(j.+1%:R)*mdist u v.
Proof.
move=> hu hv hsmall.
case: (eqVneq u v)=> [->|hne]; first by rewrite !mdistxx mulr0.
pose r := mdist u v.
have hr : 0<r by rewrite /r mdist_gt0.
have hMu := euclidean_growth_cutoff_ball_mass hu hr hsmall.
have hMv := euclidean_growth_cutoff_ball_mass hv hr hsmall.
have [x [hxu [hxv [hgu hgv]]]] := euclidean_overlap_good_point hne hMu hMv.
have hfu : mdist (f x) (f u)<=(j.+1%:R)*mdist x u.
  rewrite leNgt; apply/negP=> hbad; apply: hgu; by right.
have hfv : mdist (f x) (f v)<=(j.+1%:R)*mdist x v.
  rewrite leNgt; apply/negP=> hbad; apply: hgv; by right.
have hxur : mdist x u<=r by rewrite metric_sym; exact hxu.
have hxvr : mdist x v<=r by rewrite metric_sym; exact hxv.
have hM0 : (0<=j.+1%:R :> R) by rewrite ler0n.
have hfu' : mdist (f x) (f u)<=(j.+1%:R)*r.
  apply: (le_trans hfu _); apply: ler_wpM2l; [exact hM0|exact hxur].
have hfv' : mdist (f x) (f v)<=(j.+1%:R)*r.
  apply: (le_trans hfv _); apply: ler_wpM2l; [exact hM0|exact hxvr].
have hh := metric_triangle (f u) (f x) (f v).
rewrite (metric_sym (f u) (f x)) in hh.
change (is_true (mdist (f u) (f v)<=2*(j.+1%:R)*r)); nra.
Qed.

(** Source for [euclidean_growth_cutoff_small_piece_lipschitz]:
    the last step before using 3.1.7 in Federer 3.1.8,
    p. 218. A piece whose diameter is strictly smaller
    than 1/j has the finite positive bound 2j. *)
Lemma euclidean_growth_cutoff_small_piece_lipschitz (R : realType) m
    (Y : metricType R)
    (A E : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->Y) j :
  E `<=` euclidean_growth_cutoff A f j ->
  (forall u v, E u -> E v -> mdist u v<(j.+1%:R : R)^-1) ->
  is_metric_lipschitz E f.
Proof.
move=> hsub hdiam.
have hM : (0<2*(j.+1%:R) :> R) by apply: mulr_gt0; rewrite ltr0n.
exists (2*(j.+1%:R)); split=> //; split; first exact: ltW hM.
move=> u v hu hv.
exact: (euclidean_growth_cutoff_pair_bound (hsub u hu) (hsub v hv) (hdiam u v hu hv)).
Qed.
