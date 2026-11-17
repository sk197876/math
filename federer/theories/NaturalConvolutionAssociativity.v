(** Federer (1969), 3.4.7, p. 325: supporting the
    polynomial algebra used in the Gauss argument. The
    finite triangular rearrangement proves associativity directly. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import NaturalConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_triangular_sum_shift]: finite sum
    rearrangement supporting the coefficient algebra in
    3.4.7, p. 325; it is auxiliary algebra,
    rather than a separately printed claim. *)
Lemma finite_triangular_sum_shift (A:zmodType) n (F:nat->nat->A):
  \sum_(0<=i<n.+1) \sum_(0<=j<i.+1) F i j =
  \sum_(0<=j<n.+1) \sum_(0<=k<(n-j).+1) F (k+j)%N j.
Proof.
have hWiden : \sum_(0<=i<n.+1) \sum_(0<=j<i.+1) F i j =
    \sum_(0<=i<n.+1) \sum_(0<=j<n.+1|j<=i) F i j.
  apply:congr_big_nat=>//i /andP[_ hi].
  rewrite (big_nat_widen 0%N i.+1 n.+1 predT (fun j=>F i j) hi).
  apply:eq_bigl=>j;by rewrite andTb ltnS.
rewrite hWiden (exchange_big_dep_nat predT) //.
apply:congr_big_nat=>//j /andP[_ hj].
under eq_bigl do rewrite andTb.
rewrite -(@big_nat_widenl _ _ _ j 0%N n.+1 predT (fun i=>F i j)) //.
have hjN:(j<=n)%N by move:hj;rewrite ltnS.
rewrite -{1}(add0n j) big_addn (subSn hjN).
by [].
Qed.

(** Source for [natural_convolution_associative]: associative
    multiplication of finite coefficient expressions, supporting
    the polynomial ring in 3.4.7, p. 325. *)
Lemma natural_convolution_associative (A:comNzRingType) (f g h:nat->A) n:
  natural_coefficient_convolution (natural_coefficient_convolution f g) h n =
  natural_coefficient_convolution f (natural_coefficient_convolution g h) n.
Proof.
rewrite /natural_coefficient_convolution.
under eq_bigr do rewrite mulr_suml.
rewrite finite_triangular_sum_shift.
apply:congr_big_nat=>//j _.
rewrite mulr_sumr;apply:congr_big_nat=>//k _.
by rewrite addnK (addnC k j) subnDA mulrA.
Qed.
