(** Supporting finite indexing for Federer (1969),
    3.4.8(8), p. 330: coordinates before
    the original suffix vanish in the
    displayed primitive-coordinate sum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import OrdinalCoordinateTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [ordinal_coordinate_tail_sum]: remove
    the zero prefix from the original
    coordinate sum in 3.4.8(8), p. 330.
    Apply the existing finite-sum reindexing
    and two-block splitting identities. *)
Lemma ordinal_coordinate_tail_sum (V:zmodType) n m (hMN:(m<=n)%N) (f:'I_n->V):
  (forall i:'I_n,(i<m)%N ->f i = 0) ->
  \sum_i f i = \sum_(i<n-m) f (ordinal_coordinate_tail_index hMN i).
Proof.
move=>hZero.
pose hSum:=subnKC hMN.
have hReindex: \sum_i f i = \sum_(i<m+(n-m)) f (cast_ord hSum i).
  apply:reindex;exists (cast_ord (esym hSum)).
  - by move=>i _;apply:val_inj.
  - by move=>i _;apply:val_inj.
rewrite hReindex big_split_ord /=.
have hPrefix:(\sum_(i<m) f (cast_ord hSum (lshift (n-m) i))) = 0.
  apply:big1=>i _;apply:hZero;exact:ltn_ord i.
by rewrite hPrefix add0r.
Qed.
