(** Federer (1969), 3.4.7, p. 325: first
    nonzero coefficients of products, supporting the original
    distinguished-axis order argument. Finite coefficient sums
    prove the formulas directly. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import NaturalConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [natural_convolution_below_order]: every
    coefficient below the sum of the original
    factor orders vanishes, supporting 3.4.7, p. 325. *)
Lemma natural_convolution_below_order (A:comNzRingType) (f g:nat->A) m n k:
  (forall i,(i<m)%N ->f i = 0) ->
  (forall i,(i<n)%N ->g i = 0) ->
  (k<m+n)%N ->natural_coefficient_convolution f g k = 0.
Proof.
move=>hF hG hK;rewrite /natural_coefficient_convolution big_mkord;apply:big1=>i _.
case:(ltnP (i:nat) m)=>hI;first by rewrite hF // mul0r.
have hiK:(i<=k)%N by have:=ltn_ord i;rewrite ltnS.
have hSmall:(k-i<n)%N.
  rewrite (@ltn_subLR k i n hiK).
  exact:leq_trans hK (leq_add hI (leqnn n)).
by rewrite hG // mulr0.
Qed.

(** Source for [natural_convolution_initial_coefficient]: the
    coefficient at the sum of the original first
    nonzero indices is their product, supporting the
    order argument in 3.4.7, p. 325. *)
Lemma natural_convolution_initial_coefficient (A:comNzRingType) (f g:nat->A) m n:
  (forall i,(i<m)%N ->f i = 0) ->
  (forall i,(i<n)%N ->g i = 0) ->
  natural_coefficient_convolution f g (m+n)%N = f m*g n.
Proof.
move=>hF hG;rewrite /natural_coefficient_convolution big_mkord.
have hM:(m<(m+n).+1)%N by rewrite ltnS leq_addr.
pose index:'I_(m+n).+1:=Ordinal hM.
rewrite (bigD1 index) //= addKn.
rewrite big1 ?addr0 // =>i hi.
case:(ltngtP (i:nat) m)=>[hI|hI|hI].
- by rewrite hF // mul0r.
- have hiK:(i<=m+n)%N by have:=ltn_ord i;rewrite ltnS.
  have hSmall:(m+n-i<n)%N by rewrite (@ltn_subLR (m+n)%N i n hiK) ltn_add2r.
  by rewrite hG // mulr0.
- by move:hi;rewrite -val_eqE /= hI eqxx.
Qed.
