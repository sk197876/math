(** Federer (1969), 2.2.15, p. 71, final target criterion: pointwise
    convergence is eventually simultaneous on any fixed finite set of source
    points. This supporting lemma uses the previously proved finite
    increasing-cover argument, not uniform convergence on an infinite set. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology.
From Federer Require Import PointwiseLimit NonnegativeSumContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointwise_limit_finite_samples]: supporting
    finite-sample limit step for the necessity of the final
    criterion in Federer 2.2.15, p. 71. One stage
    works for a finite set and a prescribed positive tolerance. *)
Lemma pointwise_limit_finite_samples (R : realType) (X : choiceType) (Y : metricType R)
    (f : nat -> X -> Y) (g : X -> Y) (A : set X) (epsilon : R) :
  is_pointwise_limit f g -> finite_set A -> 0 < epsilon ->
  exists N, forall n, (N <= n)%N -> forall x, A x -> mdist (g x) (f n x) < epsilon.
Proof.
move=> hlim /finite_fsetP[F ->] he.
pose B N := [set x | forall n, (N <= n)%N -> mdist (g x) (f n x) < epsilon].
have hm n m : (n <= m)%N -> B n `<=` B m.
  move=> hnm x hx k hmk; apply: hx; exact: leq_trans hnm hmk.
have hc x : x \in F -> exists N, B N x.
  move=> hx.
  have hn : nbhs (g x) [set y | mdist (g x) y < epsilon].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP (g x) _)); by exists epsilon.
  have [N _ hN] := hlim x _ hn; exists N=> n hnn; exact: hN n hnn.
have [N hN] := @finite_increasing_cover X B F hm hc.
exists N=> n hn x hx; exact: hN x hx n hn.
Qed.
