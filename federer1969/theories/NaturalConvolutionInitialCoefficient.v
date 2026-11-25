(** Federer (1969), 3.4.8(14), p. 336:
    a product of original directional witnesses is still
    a directional witness. This supporting coefficient
    identity is the initial-order counterpart of the proved
    leading-degree identity used in 3.4.7, p. 325. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import NaturalConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [natural_convolution_initial_coefficient]: the
    first nonzero product coefficient in the finite
    product argument of 3.4.8(14), p. 336,
    computed by the original Leibniz convolution of
    3.1.11, p. 222. *)
Lemma natural_convolution_initial_coefficient (A:comNzRingType)
    (f g:nat->A) m n:
  (forall i,(i<m)%N ->f i=0) ->
  (forall i,(i<n)%N ->g i=0) ->
  natural_coefficient_convolution f g (m+n)%N=f m*g n.
Proof.
move=>hF hG.
have hM:(m<(m+n).+1)%N by rewrite ltnS leq_addr.
pose index:'I_(m+n).+1:=Ordinal hM.
rewrite /natural_coefficient_convolution big_mkord (bigD1 index) //= addKn.
rewrite big1 ?addr0 // =>i hi.
case:(ltngtP (i:nat) m)=>[hI|hI|hI].
- by rewrite hF // mul0r.
- have hBound:(i<=m+n)%N by have:=ltn_ord i;rewrite ltnS.
  have hSmall:(m+n-i<n)%N by rewrite (@ltn_subLR (m+n)%N i n hBound) ltn_add2r.
  by rewrite hG // mulr0.
- move:hi;by rewrite -val_eqE /= hI eqxx.
Qed.
