(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    global holomorphic-set dimension specified by the
    attained supremum of actual nonempty local dimensions.
    Reuse the opaque bounded-supremum interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness HolomorphicSetLocalDepth
  BoundedNaturalSupremumUP BoundedNaturalSupremumSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_set_dimension]: the supremum
    in 3.4.10, p. 337. The selected
    value is opaque through BoundedNaturalSupremum; the
    empty-set value is explicitly an auxiliary totalization. *)
Definition holomorphic_set_dimension (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)):nat:=
  @BoundedNaturalSupremum.value (coordinate_space (ComplexScalars.C R) n) S (@holomorphic_set_local_depth R n S) n
    (fun a _=>@holomorphic_set_local_depth_bound R n S a).

(** Source for [holomorphic_set_dimension_laws]: the original
    supremum laws of 3.4.10, p. 337,
    including attainment for nonempty holomorphic sets. *)
Theorem holomorphic_set_dimension_laws (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)):
  is_bounded_natural_supremum S (@holomorphic_set_local_depth R n S)
    (@holomorphic_set_dimension R n S).
Proof.
exact:(@BoundedNaturalSupremum.laws (coordinate_space (ComplexScalars.C R) n) S (@holomorphic_set_local_depth R n S) n
  (fun a _=>@holomorphic_set_local_depth_bound R n S a)).
Qed.
