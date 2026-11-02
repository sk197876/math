(** Federer (1969), 2.7.12, printed p. 129: "A group G is called unimodular
    if and only if the left and right Haar integrals of G coincide; this is
    equivalent to the condition that the modular function Delta_G is
    constant with value 1." The predicate is_unimodular states the
    definition: a functional on the real functions on G is a left Haar
    integral exactly when it is a right Haar integral, for the Haar
    integrals of HaarIntegralUP.v (2.7.2, p. 122). The equivalence with
    Delta_G = 1, and the unimodularity of compact groups, are proved in
    UnimodularGroups.v. The local erratum has no entry for p. 129. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_unimodular]: "A group G is called unimodular if
    and only if the left and right Haar integrals of G coincide",
    Federer 2.7.12, p. 129. Direct definition: the class of left Haar
    integrals equals the class of right Haar integrals. *)
Definition is_unimodular (R : realType) (G : topologicalType) (mul : G -> G -> G) (inv : G -> G) :
    Prop :=
  forall lambda : (G -> R) -> R, is_left_haar_integral mul lambda <-> is_right_haar_integral mul inv lambda.
