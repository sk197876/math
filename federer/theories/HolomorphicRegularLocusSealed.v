(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    opaque original regular part after proved unique
    existence. Only the neighbourhood laws are public. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP GrassmannAbbreviations HolomorphicRegularLocusUP HolomorphicRegularLocusExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicRegularLocusSignature.
(** Source for [value]: the regular part R
    of 3.4.10, p. 337, at the
    original global dimension. *)
Parameter value:forall (R:realType) (n m:nat),set (coordinate_space (ComplexScalars.C R) n)->set (coordinate_space (ComplexScalars.C R) n)->set (coordinate_space (ComplexScalars.C R) n).
(** Source for [laws]: the exact original neighbourhood
    criterion of 3.4.10, p. 337. *)
Parameter laws:forall (R:realType) n m (U S:set (coordinate_space (ComplexScalars.C R) n)),
  is_holomorphic_regular_locus m U S (@value R n m U S).
End HolomorphicRegularLocusSignature.
Module HolomorphicRegularLocus:HolomorphicRegularLocusSignature.
(** Source for [value]: private set selection after
    proved existence, 3.4.10, p. 337. *)
Definition value (R:realType) n m (U S:set (coordinate_space (ComplexScalars.C R) n)):=
  projT1 (cid (@holomorphic_regular_locus_exists R n m U S)).
(** Source for [laws]: the selected regular part
    satisfies the independent original condition,
    3.4.10, p. 337. *)
Lemma laws (R:realType) n m (U S:set (coordinate_space (ComplexScalars.C R) n)):
  is_holomorphic_regular_locus m U S (@value R n m U S).
Proof. exact:(projT2 (cid (@holomorphic_regular_locus_exists R n m U S))). Qed.
End HolomorphicRegularLocus.
