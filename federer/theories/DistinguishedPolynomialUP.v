(** Federer (1969), 3.4.7, p. 325, using
    3.4.6(2), p. 322: the prepared polynomial is
    monic and its lower transverse coefficients vanish at
    the origin. The predicate asserts no existence or
    analytic primality conclusion. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialMonicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_distinguished_polynomial]: the original
    degree, leading coefficient one, and vanishing lower
    coefficient values used in the Weierstrass factor
    argument of 3.4.7, p. 325. *)
Definition is_distinguished_polynomial (A C:comNzRingType) (B:Type)
    (coefficient:B->nat->A) (value:{rmorphism A->C}) (P:B) k:Prop:=
  is_monic_polynomial coefficient P k /\
  forall i,(i<k)%N ->value (coefficient P i) = 0.
