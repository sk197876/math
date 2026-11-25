(** Federer (1969), 2.10.21, p. 184: a finite-dimensional normed vector
    space satisfies the bounded compactness needed by the preceding
    Hausdorff family argument. Use the project's already proved compact norm
    balls and translations. it is not an attribution of this elementary
    topology adapter. Source context: NormSubconvexCompact.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric MetricClosedBalls LinearBasis FiniteNormMetricCompactness
  FiniteNormCompactHull LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_metric_boundedly_compact]: supporting
    finite-dimensional bounded compactness for the
    compact convex-family assertion in 2.10.21,
    p. 184. Arbitrary norms and dimension zero are retained. *)
Theorem finite_norm_metric_boundedly_compact (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) d (e : 'I_d -> V) :
  is_basis e -> metric_boundedly_compact (real_norm_metric_space hN).
Proof.
move=> he a r hr.
have hball := @finite_norm_metric_ball_compact R V N hN d e he r.
have heq : @metric_closed_ball R (real_norm_metric_space hN) a r=
    (fun x : real_norm_metric_space hN => (x+a : real_norm_metric_space hN)) @` [set x | N x<=r].
  apply/seteqP; split=> x hx.
  - exists (x-a); last by rewrite subrK.
    have hh : N (a-x)<=r := hx.
    change (is_true (N (x-a)<=r)); by rewrite (real_seminorm_subtract hN.1 x a).
  - have [y hy <-] := hx.
    change (is_true (N (a-(y+a))<=r)).
    by rewrite (real_seminorm_subtract hN.1 a (y+a)) addrK.
rewrite heq; apply: continuous_compact hball.
have ht := @norm_translation_continuous R V N hN a.
exact: continuous_subspaceT ht.
Qed.
