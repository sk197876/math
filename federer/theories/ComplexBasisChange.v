(** Federer (1969), 1.6.6, p. 27: the automorphism carrying one complex
    basis to another. Its inverse is constructed from the two basis
    coordinate maps; no choice of an ambient finite space is required.
    Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates ComplexScalarSealed ComplexDeterminant
  ComplexCharacteristic ComplexOrderedBases ScalarRestriction ExteriorDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Change.
Variable K : fieldType.
Variable V : lmodType K.
Variable I : choiceType.
Variables v w : I -> V.
Hypothesis hv : is_basis v.

(** Source for [basis_change_map]: Federer 1.6.6, p. 27,
    the automorphism g mapping v_j onto w_j. A linear map specified
    by its basis values, constructed from the basis universal property. *)
Definition basis_change_map := linear_comp (basis_synthesis w) (basis_coordinates hv).

(** Source for [basis_change_mapE]: Federer 1.6.6, p. 27,
    g(v_j)=w_j. Verification of the defining values. *)
Lemma basis_change_mapE j : basis_change_map (v j) = w j.
Proof. by rewrite /basis_change_map /= basis_coordinatesE basis_synthesisE. Qed.
End Change.

(** Source for [basis_change_mapK]: Federer 1.6.6, p. 27,
    the change of complex basis is an automorphism. Interchanging
    the two bases supplies the inverse. *)
Lemma basis_change_mapK (K : fieldType) (V : lmodType K) (I : choiceType)
  (v w : I -> V) (hv : is_basis v) (hw : is_basis w) :
  cancel (basis_change_map w hv) (basis_change_map v hw).
Proof.
move=> x; change (basis_synthesis v (basis_coordinates hw (basis_synthesis w (basis_coordinates hv x))) = x).
by rewrite basis_synthesisK basis_coordinatesK.
Qed.

(** Source for [complex_basis_change_positive]: Federer 1.6.6,
    p. 27, the determinant of the complex change of basis is positive
    over R. This is the positivity used to make sign(r) intrinsic. *)
Lemma complex_basis_change_positive (R : realFieldType) (V : lmodType (ComplexScalars.C R))
  p (v w : 'I_p -> V) (hv : is_basis v) (hw : is_basis w) :
  0 < det (real_two_nonzero R) (ordered_real_basisP hv)
    (restrict_linear (ComplexScalars.embed R) (basis_change_map w hv)).
Proof.
exact: (@complex_automorphism_determinant_positive R V p v hv
  (basis_change_map w hv) (basis_change_map v hw) (basis_change_mapK hv hw)).
Qed.
