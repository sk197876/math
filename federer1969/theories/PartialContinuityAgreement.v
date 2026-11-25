(** Federer (1969), 2.3.6, p. 77: replacing the restricted
    function by an agreeing total representative for Tietze, and
    transferring continuity from a separable subspace. Source
    editions: ContinuousClosedPieceBorel.v. This is supporting
    general topology for single-valued partial graphs. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_continuity_agreement]: supporting continuity
    transfer on C in Federer 2.3.6, p. 77. Agreement means
    both functions are defined there and have the same value. *)
Lemma partial_continuity_agreement (X Y : topologicalType) (C : set X)
    (f g : partial_function X Y) : C `<=` partial_function_agreement f g ->
  partial_function_continuous_on C f -> partial_function_continuous_on C g.
Proof.
move=> ha hf; constructor.
- move=> x hx; have [y [_ hy]] := ha x hx; by exists y.
- move=> U hU; have [V [hV he]] := partial_continuity_open hf hU.
  exists V; split=> //.
  have heq : C `&` partial_function_preimage g U = C `&` partial_function_preimage f U.
    apply/seteqP; split=> x [hx [y [hy huy]]]; split=> //.
    + have [z [hzf hzg]] := ha x hx.
      have hz := @partial_function_single_valued X Y g x z y hzg hy.
      exists y; split=> //; by rewrite -hz.
    + have [z [hzf hzg]] := ha x hx.
      have hz := @partial_function_single_valued X Y f x z y hzf hy.
      exists y; split=> //; by rewrite -hz.
  by rewrite heq.
Qed.
