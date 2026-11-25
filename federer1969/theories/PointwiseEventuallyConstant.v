(** Federer (1969), 2.2.15, p. 71: supporting pointwise convergence for
    characteristic-function approximants and finite-union approximants.
    Eventual equality at each source point is sufficient, with no uniform
    stage required. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PointwiseLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointwise_eventually_equal_limit]: supporting
    convergence criterion for the characteristic-function steps of
    Federer 2.2.15, p. 71. The eventual stage may
    depend on the source point. *)
Lemma pointwise_eventually_equal_limit (X : Type) (Y : topologicalType)
    (f : nat -> X -> Y) (g : X -> Y) :
  (forall x, exists N, forall n, (N <= n)%N -> f n x = g x) ->
  is_pointwise_limit f g.
Proof.
move=> h x V hV; have [N hN] := h x.
exists N; first exact Logic.I.
move=> n hn; change (V (f n x)); rewrite hN //; exact: nbhs_singleton hV.
Qed.
