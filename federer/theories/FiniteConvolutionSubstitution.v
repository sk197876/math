(** Federer (1969), 3.4.7, p. 325: substituting an
    arbitrary ring element into finite coefficient expressions
    preserves multiplication. Finite triangular sums prove the
    identity without an external polynomial implementation. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import NaturalConvolution NaturalConvolutionAssociativity FinitePrefixSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_convolution_substitution_product]: convolution
    of finite coefficients evaluates to the product of
    their original expressions, supporting polynomial evaluation
    in 3.4.7, p. 325. *)
Theorem finite_convolution_substitution_product (C:comNzRingType)
    (f g:nat->C) N M (t:C):
  (forall i,(N<=i)%N ->f i = 0) ->
  (forall i,(M<=i)%N ->g i = 0) ->
  (\sum_(i<N) f i*t^+i)*(\sum_(j<M) g j*t^+j) =
    \sum_(k<(N+M).+1) natural_coefficient_convolution f g k*t^+k.
Proof.
move=>hF hG.
have hFZero i:(N<=i)%N ->f i*t^+i = 0 by move=>hi;rewrite hF // mul0r.
have hGZero i:(M<=i)%N ->g i*t^+i = 0 by move=>hi;rewrite hG // mul0r.
have hNL:(N<=(N+M).+1)%N:=leq_trans (leq_addr M N) (leqnSn _).
have hML:(M<=(N+M).+1)%N:=leq_trans (leq_addl N M) (leqnSn _).
rewrite (@finite_prefix_sum_extend C (fun i=>f i*t^+i) N (N+M).+1 hNL hFZero)
  (@finite_prefix_sum_extend C (fun i=>g i*t^+i) M (N+M).+1 hML hGZero).
symmetry.
have hTriangle:(\sum_(k<(N+M).+1) natural_coefficient_convolution f g k*t^+k) =
    \sum_(i<(N+M).+1) \sum_(j<(N+M-i).+1) (f i*g j)*t^+(j+i).
  transitivity (\sum_(0<=k<(N+M).+1)
    \sum_(0<=i<k.+1) (f i*g (k-i)%N)*t^+k).
  - rewrite big_mkord;apply:eq_bigr=>k _.
    by rewrite /natural_coefficient_convolution mulr_suml.
  - rewrite finite_triangular_sum_shift big_mkord.
    apply:eq_bigr=>i _;rewrite big_mkord;apply:eq_bigr=>j _.
    by rewrite addnK.
rewrite hTriangle mulr_suml.
apply:eq_bigr=>i _;rewrite mulr_sumr.
have hInnerBound:((N+M-i).+1<=(N+M).+1)%N by rewrite !ltnS leq_subr.
rewrite (@big_ord_widen _ _ _ (N+M-i).+1 (N+M).+1
  (fun j=>(f i*g j)*t^+(j+i)) hInnerBound) big_mkcond.
apply:eq_bigr=>j _.
case:(ltnP (j:nat) (N+M-i).+1)=>hJ.
- by rewrite exprD (mulrC (t^+j) (t^+i)) mulrACA.
- have hZero:f i*g j = 0.
    case:(leqP N (i:nat))=>hI;first by rewrite hF // mul0r.
    have hIJ:(N+M<=i+j)%N by rewrite -leq_subLR;exact:ltnW hJ.
    have hMJ:=leq_trans hIJ (leq_add (ltnW hI) (leqnn j)).
    rewrite leq_add2l in hMJ.
    by rewrite hG // mulr0.
  have hProduct:(f i*t^+i)*(g j*t^+j) = (f i*g j)*t^+(j+i).
    by rewrite exprD (mulrC (t^+j) (t^+i)) mulrACA.
  by rewrite hProduct hZero mul0r.
Qed.
