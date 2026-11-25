(** Federer (1969), 3.4.6(2), p. 322: the
    lower zero axis coefficients isolate the first nonzero
    product coefficient in the preparation argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_axis_product_below]: a
    factor of original directional order k makes all
    lower axis product coefficients zero, supporting
    3.4.6(2), p. 322. *)
Lemma weierstrass_axis_product_below (R:realType) k (phi q:nat->R):
  (forall i,(i<k)%N ->phi i=0) ->forall i,(i<k)%N ->
    (\sum_(mu<i.+1) phi (i-mu)%N*q mu)=0.
Proof.
move=>hLow i hi;apply:big1=>mu _.
have hSmall:(i-mu<k)%N:=leq_ltn_trans (leq_subr mu i) hi.
by rewrite (hLow _ hSmall) mul0r.
Qed.

(** Source for [weierstrass_axis_product_leading]: the
    original first nonzero product coefficient is exactly
    phi_(k,0) times Q_(0,0), supporting Q(0) nonzero
    in 3.4.6(2), p. 322. *)
Lemma weierstrass_axis_product_leading (R:realType) k (phi q:nat->R):
  (forall i,(i<k)%N ->phi i=0) ->
    (\sum_(mu<k.+1) phi (k-mu)%N*q mu)=phi k*q 0%N.
Proof.
move=>hLow;rewrite (bigD1 (Ordinal (ltn0Sn k))) //= subn0.
have hOthers:(\sum_(mu<k.+1 | mu!=Ordinal (ltn0Sn k)) phi (k-mu)%N*q mu)=0.
  apply:big1=>mu hMu.
  have hPositive:(0<mu)%N by rewrite lt0n;move:hMu;rewrite -val_eqE /=.
  have hLe:(mu<=k)%N by have:=ltn_ord mu;rewrite ltnS.
  have hLess:(k-mu<k)%N.
    rewrite (@ltn_subLR k mu k hLe) -[X in (X<_ )%N](add0n k) ltn_add2r.
    exact:hPositive.
  by rewrite (hLow _ hLess) mul0r.
by rewrite hOthers addr0.
Qed.
