(** Federer (1969), 3.4.7, p. 325: the
    original coefficient and polynomial rings in the
    factorization argument have no zero divisors.
    This supporting predicate separates that algebraic law
    from factorization existence and uniqueness. *)
From mathcomp Require Import all_boot ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_commutative_integral_domain]: absence
    of proper zero divisors, required by the
    Gauss argument of 3.4.7, p. 325.
    The underlying ring already has one different from zero. *)
Definition is_commutative_integral_domain (A:comNzRingType):Prop:=
  forall x y:A,x*y = 0 ->x = 0 \/y = 0.
