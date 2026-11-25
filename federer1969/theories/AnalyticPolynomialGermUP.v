(** Supporting Federer (1969), 3.4.8(5), p. 328:
    original polynomial functions define their actual analytic germs.
    State the representative law before proving existence or exposing
    linearity, derivatives or finite-jet interpolation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP PolynomialFunctions AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_analytic_polynomial_germ_map]: the original
    polynomial-to-germ connection supporting Federer 3.4.8(5), p. 328,
    from the polynomial functions of 1.10.4, p. 46 and the local ring
    of 3.4.5, p. 319. Every polynomial has its exact global function
    as a representative; no algebraic or derivative conclusion is assumed. *)
Definition is_analytic_polynomial_germ_map (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX a):Prop:=
  forall P:PolynomialFunction X R^o,exists p:@analytic_representative_type R X NX hNX a,
    (forall x,analytic_representative_value p x = P x) /\J P = analytic_germ p.
