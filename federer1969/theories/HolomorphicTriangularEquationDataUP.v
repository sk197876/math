(** Federer (1969), 3.4.12, p. 339, extending
    3.4.8(11), p. 333: independent finite triangular-equation
    laws for the depth-zero proof. This supporting data package
    makes no existence or isolated-zero assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed FiniteCoordinates
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing FieldPrefixCoordinatesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Data.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable n:nat.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable Ig:set (@holomorphic_germ_ring R X NX hNX 0).
Variable j:'I_n.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) j).
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation P:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega j hJN).
(** Source for [holomorphic_triangular_equation_data]: one original
    prepared monic equation in the simultaneous depth-zero argument,
    3.4.8(11), p. 333, under 3.4.12, p. 339.
    These independent laws precede their existence proof. *)
Record holomorphic_triangular_equation_data:Type:={
  (** Source for [holomorphic_triangular_degree]: the original positive
      Weierstrass degree, 3.4.8(11), p. 333. *)
  holomorphic_triangular_degree:nat;
  (** Source for [holomorphic_triangular_coefficients]: the lower original
      prefix coefficients, 3.4.8(11), p. 333. *)
  holomorphic_triangular_coefficients:'I_holomorphic_triangular_degree->Y->ComplexScalars.C R;
  (** Source for [holomorphic_triangular_function]: an actual original
      ambient representative, 3.4.8(11), p. 333. *)
  holomorphic_triangular_function:@holomorphic_representative_type R X NX hNX 0;
  (** Source for [holomorphic_triangular_laws]: positivity, vanishing lower
      centre coefficients, original ideal membership and the exact
      monic value equation, 3.4.8(11), p. 333. *)
  holomorphic_triangular_laws:
    (0<holomorphic_triangular_degree)%N /\
    (forall i,holomorphic_triangular_coefficients i 0 = 0) /\
    Ig (holomorphic_germ holomorphic_triangular_function) /\
    forall x,holomorphic_representative_value holomorphic_triangular_function x =
      (omega j x)^+holomorphic_triangular_degree+
      \sum_(i<holomorphic_triangular_degree) holomorphic_triangular_coefficients i (P x)*(omega j x)^+(i:nat)
}.
End Data.
