(** Federer (1969), 3.4.7, p. 325: changing the
    original coefficients to their fractions in the Gauss
    argument. Coefficient equations specify the map independently. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_polynomial_coefficient_map]: the original
    coefficient homomorphism acts coefficient by coefficient,
    supporting the comparison in 3.4.7, p. 325.
    Existence, injectivity and factorization are separate proofs. *)
Definition is_polynomial_coefficient_map (A C:comNzRingType) (B D:Type)
    (source:B->nat->A) (target:D->nat->C) (phi:{rmorphism A->C}) (map:B->D):Prop:=
  forall P i,target (map P) i = phi (source P i).
