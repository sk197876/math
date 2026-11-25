(** Federer (1969), 3.4.7, p. 325: monomial
    coefficient arithmetic supporting the abstract polynomial extension. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import NaturalConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [natural_convolution_monomial]: a single
    coefficient shifts the other factor, supporting the
    polynomial expressions in 3.4.7, p. 325. *)
Lemma natural_convolution_monomial (A:comNzRingType) d (a:A) (f:nat->A) n:
  natural_coefficient_convolution (fun i=>if i==d then a else 0) f n =
    if (d<=n)%N then a*f (n-d)%N else 0.
Proof.
rewrite /natural_coefficient_convolution big_mkord.
case:(leqP d n)=>hDn.
- have hd:(d<n.+1)%N by rewrite ltnS.
  pose index:'I_n.+1:=Ordinal hd.
  rewrite (bigD1 index) //= eqxx.
  rewrite big1 ?addr0 // =>i hi.
  have hiD:((i:nat)==d) = false.
    apply/negP=>/eqP h;move:hi;by rewrite -val_eqE /= h eqxx.
  by rewrite hiD mul0r.
- apply:big1=>i _.
  have hiD:((i:nat)==d) = false.
    apply/negP=>/eqP h.
    have hi:(i<=n)%N by have:=ltn_ord i;rewrite ltnS.
    move:hi;by rewrite h (ltn_geF hDn).
  by rewrite hiD mul0r.
Qed.
