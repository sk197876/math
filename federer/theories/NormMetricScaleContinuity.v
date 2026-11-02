(** Normed-space topology supporting Federer (1969), 2.3.8, pp. 78–79:
    scalar multiplication is continuous in either variable. Source context:
    NormMetricContinuity.v. These background facts are derived directly from
    the supplied norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_fixed_lipschitz_continuous]: supporting
    general-topology fact for Federer 2.3.8, pp. 78–79:
    a nonnegative finite Lipschitz bound implies continuity. *)
Lemma metric_fixed_lipschitz_continuous (R : realType) (T U : metricType R)
    (f : T -> U) (L : R) : 0 <= L ->
  (forall x y, mdist (f x) (f y) <= L * mdist x y) -> continuous f.
Proof.
move=> hL hb x W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (f x) W) hW.
have hpos : 0 < 1+L by rewrite ltr_pwDl.
have hd : 0 < e/(1+L) by rewrite divr_gt0.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
exists (e/(1+L))=> // y hy; apply: hball.
apply: le_lt_trans (hb x y) _.
have hle : L * mdist x y <= (1+L)*mdist x y.
  apply: ler_wpM2r; first exact: mdist_ge0.
  by rewrite lerDr.
apply: le_lt_trans hle _.
rewrite mulrC -ltr_pdivlMr //; exact hy.
Qed.

(** Source for [real_norm_metric_scale_continuous]: continuity
    of multiplication by a fixed scalar for the function-space
    operations of Federer 2.3.8, pp. 78–79. *)
Lemma real_norm_metric_scale_continuous (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (c : R) :
  continuous (fun x : real_norm_metric_space hN => (c *: x : real_norm_metric_space hN)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ `|c| (normr_ge0 c)).
move=> x y; change (N (c *: x-c *: y) <= `|c|*N (x-y)).
by rewrite -scalerBr (real_seminorm_scale hN.1).
Qed.

(** Source for [real_norm_metric_scalar_orbit_continuous]: continuity in the
    scalar for a fixed vector, supporting the separable linear-span
    reduction in Federer 2.3.8, p. 78 *)
Lemma real_norm_metric_scalar_orbit_continuous (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (x : V) :
  continuous (fun c : real_line_metric R => (c *: x : real_norm_metric_space hN)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ (N x) (real_seminorm_nonnegative hN.1 x)).
move=> a b; change (N (a *: x-b *: x) <= N x * `|a-b|).
by rewrite -scalerBl (real_seminorm_scale hN.1) mulrC.
Qed.
