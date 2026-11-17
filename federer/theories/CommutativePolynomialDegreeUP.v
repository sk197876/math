(** Federer (1969), 3.4.7, p. 325: degree and
    leading coefficient in the polynomial algebra used by
    Gauss's lemma. These predicates assert no factorization theorem. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_polynomial_degree]: a nonzero leading
    coefficient and vanishing higher coefficients specify the
    degree used in 3.4.7, p. 325. *)
Definition is_polynomial_degree (A:comNzRingType) (B:Type)
    (coefficient:B->nat->A) (P:B) d:Prop:=
  coefficient P d<>0 /\forall i,(d<i)%N ->coefficient P i = 0.

(** Source for [is_primitive_polynomial]: no original prime
    divides all coefficients, the primitive-polynomial condition
    supporting the Gauss lemma in 3.4.7, p. 325.
    It is specified without choosing a content or gcd. *)
Definition is_primitive_polynomial (A:comNzRingType) (B:Type)
    (coefficient:B->nat->A) (prime:A->Prop) (divides:A->A->Prop) (P:B):Prop:=
  forall p,prime p ->exists i,~divides p (coefficient P i).
