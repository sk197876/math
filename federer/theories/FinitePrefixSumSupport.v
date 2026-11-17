(** Federer (1969), 3.4.7, p. 325: finite
    coefficient expressions do not depend on trailing zeros.
    This supporting sum fact supplies polynomial evaluation. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_prefix_sum_extend]: padding a
    finite sum by original zero terms leaves its
    value unchanged, supporting polynomial substitution in
    3.4.7, p. 325. *)
Lemma finite_prefix_sum_extend (V:zmodType) (f:nat->V) N M:
  (N<=M)%N ->(forall i,(N<=i)%N ->f i = 0) ->
  \sum_(i<N) f i = \sum_(i<M) f i.
Proof.
move=>hNM hZero;rewrite (@big_ord_widen _ _ _ N M f hNM) big_mkcond.
apply:eq_bigr=>i _;case:(ltnP (i:nat) N)=>hi;first by [].
exact:esym (hZero i hi).
Qed.

(** Source for [finite_prefix_sum_support_independent]: two
    actual support bounds yield the same finite sum,
    supporting the evaluation existence proof for
    3.4.7, p. 325. *)
Lemma finite_prefix_sum_support_independent (V:zmodType) (f:nat->V) N M:
  (forall i,(N<=i)%N ->f i = 0) ->
  (forall i,(M<=i)%N ->f i = 0) ->
  \sum_(i<N) f i = \sum_(i<M) f i.
Proof.
move=>hN hM.
rewrite (@finite_prefix_sum_extend V f N (maxn N M) (leq_maxl _ _) hN).
exact:esym (@finite_prefix_sum_extend V f M (maxn N M) (leq_maxr _ _) hM).
Qed.
