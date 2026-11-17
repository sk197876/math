(** Federer (1969), 3.4.7, p. 325: leading terms
    of products, supporting degree arithmetic in the Gauss argument. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import NaturalConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [natural_convolution_above_degree]: coefficients
    above the sum of factor degrees vanish, supporting
    3.4.7, p. 325. *)
Lemma natural_convolution_above_degree (A:comNzRingType) (f g:nat->A) m n k:
  (forall i,(m<i)%N ->f i = 0) ->
  (forall i,(n<i)%N ->g i = 0) ->
  (m+n<k)%N ->natural_coefficient_convolution f g k = 0.
Proof.
move=>hF hG hK;rewrite /natural_coefficient_convolution big_mkord;apply:big1=>i _.
case:(leqP i m)=>hI;last by rewrite hF // mul0r.
have hNi:(n<k-i)%N.
  rewrite ltn_subRL.
  exact:leq_ltn_trans (leq_add hI (leqnn n)) hK.
by rewrite hG // mulr0.
Qed.

(** Source for [natural_convolution_leading_coefficient]: the
    leading product coefficient is the product of the
    original leading coefficients, supporting 3.4.7, p. 325. *)
Lemma natural_convolution_leading_coefficient (A:comNzRingType) (f g:nat->A) m n:
  (forall i,(m<i)%N ->f i = 0) ->
  (forall i,(n<i)%N ->g i = 0) ->
  natural_coefficient_convolution f g (m+n)%N = f m*g n.
Proof.
move=>hF hG;rewrite /natural_coefficient_convolution big_mkord.
have hM:(m<(m+n).+1)%N by rewrite ltnS leq_addr.
pose index:'I_(m+n).+1:=Ordinal hM.
rewrite (bigD1 index) //= addKn.
rewrite big1 ?addr0 // =>i hi.
case:(ltngtP (i:nat) m)=>[hI|hI|hI];last first.
- move:hi;by rewrite -val_eqE /= hI eqxx.
- by rewrite hF // mul0r.
- have hNi:(n<m+n-i)%N by rewrite ltn_subRL ltn_add2r.
  by rewrite hG // mulr0.
Qed.
