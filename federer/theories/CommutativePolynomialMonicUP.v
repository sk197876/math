(** Federer (1969), 3.4.7, p. 325: the monic
    polynomials supplied by preparation and used in factorization.
    Degree and leading coefficient specify monicity independently
    of any factorization or analytic prime assertion. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialDegreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_monic_polynomial]: an actual polynomial
    has the given degree and leading coefficient one,
    supporting the Weierstrass factors in 3.4.7, p. 325. *)
Definition is_monic_polynomial (A:comNzRingType) (B:Type)
    (coefficient:B->nat->A) (P:B) n:Prop:=
  is_polynomial_degree coefficient P n /\coefficient P n = 1.
