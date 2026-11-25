(** Federer (1969), 4.1.12, p. 368: the
    two literal original endpoint families are exactly
    the even and odd dyadic powers. Retain the
    original k>=1 indexing, with formal n denoting
    k=n+1, and the full endpoint set with zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra ring.
From Federer Require Import DyadicCurrentEndpointArithmetic DyadicEndpointSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dyadic_current_left_endpoint_index]: the
    original 2^(-2k) is the dyadic endpoint of
    formal index 2n+1 when k=n+1, supporting
    Federer 4.1.12, p. 368. *)
Lemma dyadic_current_left_endpoint_index (R:realType) n:
  dyadic_current_left_endpoint R n=dyadic_endpoint_point R (2*n+1)%N.
Proof.
have hIndex:((2*n+1).+1= 2*n.+1)%N by rewrite mulnS !addnS !addn0.
have hQuarter:(1/2:R)^+2= 1/4 by field;by rewrite ?pnatr_eq0.
by rewrite /dyadic_current_left_endpoint /dyadic_endpoint_point hIndex exprM hQuarter.
Qed.

(** Source for [dyadic_current_endpoint_point_injective]:
    the original dyadic endpoints are all
    distinct, supporting the bounded endpoint tests
    in Federer 4.1.12, p. 368. *)
Lemma dyadic_current_endpoint_point_injective (R:realType):
  injective (dyadic_endpoint_point R).
Proof.
have hQ:0<(1/2:R) by lra.
have hNotOne:(1/2:R)!=1 by apply/eqP=>h;lra.
move=>i j hEqual.
have hSuccessor:i.+1=j.+1:=ieexprIn hQ hNotOne hEqual.
exact:succn_inj hSuccessor.
Qed.

(** Source for [dyadic_current_right_endpoint_index]: the
    original 2^(1-2k) is the dyadic endpoint of
    formal index 2n when k=n+1, supporting
    Federer 4.1.12, p. 368. *)
Lemma dyadic_current_right_endpoint_index (R:realType) n:
  dyadic_current_right_endpoint R n=dyadic_endpoint_point R (2*n)%N.
Proof.
rewrite /dyadic_current_right_endpoint dyadic_current_left_endpoint_index addn1 dyadic_endpoint_next.
by rewrite mulrC divfK ?pnatr_eq0.
Qed.

(** Source for [dyadic_current_left_endpoint_in_set]: every
    literal original left endpoint lies in the
    actual compact endpoint set, supporting Federer
    4.1.12, p. 368. *)
Lemma dyadic_current_left_endpoint_in_set (R:realType) n:
  dyadic_endpoint_set R (dyadic_current_left_endpoint R n).
Proof.
rewrite dyadic_current_left_endpoint_index;right;exists (2*n+1)%N;by [].
Qed.

(** Source for [dyadic_current_right_endpoint_in_set]: every
    literal original right endpoint lies in the
    actual compact endpoint set, supporting Federer
    4.1.12, p. 368. *)
Lemma dyadic_current_right_endpoint_in_set (R:realType) n:
  dyadic_endpoint_set R (dyadic_current_right_endpoint R n).
Proof.
rewrite dyadic_current_right_endpoint_index;right;exists (2*n)%N;by [].
Qed.

(** Source for [dyadic_current_opposite_endpoints_distinct]:
    no original left endpoint equals an
    original right endpoint, supporting the finite
    mass witnesses in Federer 4.1.12, p. 368. *)
Lemma dyadic_current_opposite_endpoints_distinct (R:realType) i j:
  dyadic_current_left_endpoint R i<>dyadic_current_right_endpoint R j.
Proof.
rewrite dyadic_current_left_endpoint_index dyadic_current_right_endpoint_index.
move=>hEqual.
have hIndex:=dyadic_current_endpoint_point_injective hEqual.
have hOdd:=congr1 odd hIndex.
by rewrite oddD !oddM /= in hOdd.
Qed.

(** Source for [dyadic_current_right_endpoints_injective]:
    the original right endpoints are distinct,
    supporting the endpoint test values in
    Federer 4.1.12, p. 368. *)
Lemma dyadic_current_right_endpoints_injective (R:realType):
  injective (dyadic_current_right_endpoint R).
Proof.
move=>i j;rewrite !dyadic_current_right_endpoint_index=>hEqual.
have hIndex:=dyadic_current_endpoint_point_injective hEqual.
apply/eqP;have hBool:((2*i)%N==(2*j)%N) by apply/eqP.
by move:hBool;rewrite eqn_mul2l /=.
Qed.
