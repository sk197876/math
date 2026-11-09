(** Federer (1969), 3.4.5, p. 321, referring to
    Cartan (1957), pp. 97–99: a locally analytic surface
    need not admit global analytic defining equations.
    This version uses the same cubic surface with the
    one-sided flat coefficient exp(-(1-z)^-2), extended by
    zero for z>=1. The altered coefficient removes the
    unused second flat endpoint; non-globality must be proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations FlatExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_cartan_flat_surface]: the original
    cubic surface pattern z(x^2+y^2)=x^3 a(z), Cartan
    pp. 97–98, cited in 3.4.5, p. 321.
    This specification states only actual membership and
    assumes no analyticity, closedness or non-globality. *)
Record is_cartan_flat_surface (R:realType) (S:set (R_n R 3)):Prop:={
  (** Source for [cartan_surface_membership]: actual cubic
      membership, with the stated one-sided flat coefficient,
      supporting the counterexample cited in 3.4.5, p. 321. *)
  cartan_surface_membership:forall v,S v <->
    v ord_max*((v ord0)^+2+(v (Ordinal (isT:(1<3)%N)))^+2)=
      (v ord0)^+3*FlatExponential.value (1-v ord_max)
}.
