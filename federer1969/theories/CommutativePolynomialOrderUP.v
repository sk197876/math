(** Federer (1969), 3.4.7, p. 325: the
    first nonzero coefficient determines order on the
    distinguished axis. This independent predicate supports
    the factor comparison with the original power t^k. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_polynomial_order]: the original
    first nonzero coefficient and vanishing lower coefficients,
    supporting the positive-order factor comparison in
    3.4.7, p. 325. *)
Definition is_polynomial_order (A:comNzRingType) (B:Type)
    (coefficient:B->nat->A) (P:B) n:Prop:=
  coefficient P n<>0 /\forall i,(i<n)%N ->coefficient P i = 0.
