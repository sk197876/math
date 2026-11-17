(** Federer (1969), 3.4.7, p. 325: supporting finite
    coefficient arithmetic for the simple transcendental extension.
    These identities expand the algebra implicit in the Gauss lemma. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [natural_coefficient_convolution]: the coefficient
    product in the polynomial extension used in 3.4.7,
    p. 325, written as a finite natural-index sum. *)
Definition natural_coefficient_convolution (A:comNzRingType)
    (f g:nat->A) n:A:=\sum_(0<=i<n.+1) f i*g (n-i)%N.

(** Source for [natural_convolution_zero]: the zero polynomial
    annihilates a product, supporting 3.4.7, p. 325. *)
Lemma natural_convolution_zero (A:comNzRingType) (f:nat->A) n:
  natural_coefficient_convolution (fun _=>0) f n = 0.
Proof. apply:big1=>i _;exact:mul0r. Qed.

(** Source for [natural_convolution_add]: distributivity of the
    coefficient product, supporting 3.4.7, p. 325. *)
Lemma natural_convolution_add (A:comNzRingType) (f g h:nat->A) n:
  natural_coefficient_convolution (fun i=>f i+g i) h n =
  natural_coefficient_convolution f h n+natural_coefficient_convolution g h n.
Proof. rewrite /natural_coefficient_convolution -big_split;apply:eq_bigr=>i _;exact:mulrDl. Qed.

(** Source for [natural_convolution_commutative]: symmetry of the
    coefficient product, supporting 3.4.7, p. 325. *)
Lemma natural_convolution_commutative (A:comNzRingType) (f g:nat->A) n:
  natural_coefficient_convolution f g n = natural_coefficient_convolution g f n.
Proof.
rewrite /natural_coefficient_convolution big_nat_rev.
apply:congr_big_nat=>//i /andP[_ hi].
have hiN:(i<=n)%N by move:hi;rewrite ltnS.
rewrite add0n subSS (subKn hiN).
exact:mulrC.
Qed.

(** Source for [natural_convolution_one]: the constant unit is
    the coefficient-product unit, supporting 3.4.7, p. 325. *)
Lemma natural_convolution_one (A:comNzRingType) (f:nat->A) n:
  natural_coefficient_convolution (fun i=>if i==0%N then 1 else 0) f n = f n.
Proof.
rewrite /natural_coefficient_convolution big_mkord (bigD1 (ord0:'I_n.+1)) //= subn0 mul1r.
rewrite big1 ?addr0 // =>i hi.
have hi0:((i:nat)==0%N) = false.
  apply/negP=>/eqP h;move:hi;by rewrite -val_eqE /= h eqxx.
by rewrite hi0 mul0r.
Qed.
