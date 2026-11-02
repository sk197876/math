(** Federer (1969), 2.4.12, pp. 87–88: decomposition of finite-image
    functions into elementary fibre pieces. The supporting finite-sum
    identity below is purely algebraic. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_delta_vector_sum]: supporting pointwise
    reconstruction for the finite-image argument in Federer 2.4.12,
    pp. 87–88. Distinct labels prevent counting a value twice. *)
Lemma finite_delta_vector_sum (R : fieldType) (V : lmodType R)
    (s : seq V) (v : V) (c : V -> R) :
  uniq s -> v \in s -> c v = 1 -> (forall u, u != v -> c u=0) ->
  \sum_(u <- s) c u *: u = v.
Proof.
move=> hs hv hc hzero; rewrite (bigD1_seq v) // hc scale1r.
have he : \sum_(u <- s | u != v) c u *: u = 0.
  apply: big1=> u hu; by rewrite (hzero u hu) scale0r.
rewrite he; change (v+0=v); by rewrite addr0.
Qed.
