(** Federer (1969), 1.6.6, p. 27: change of complex basis multiplies the
    paired real volume by a positive determinant. Naturality transfers the
    claim to any ambient complex space. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ExteriorMaps ExteriorDeterminant
  ComplexScalarSealed ComplexCharacteristic ScalarRestriction ComplexPairedVectors
  ComplexOrderedBases ComplexBasisChange ComplexDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [paired_complex_vector_natural]: Federer
    1.6.6, p. 27, the automorphism g sends every real-imaginary
    pair to the corresponding new pair. This holds for every complex
    linear map, including subspace inclusions. *)
Lemma paired_complex_vector_natural (R : realFieldType)
  (V W : lmodType (ComplexScalars.C R)) (f : {linear V -> W})
  p (v : 'I_p -> V) :
  exterior_power_map (restrict_linear (ComplexScalars.embed R) f) (p+p)
    (paired_complex_vector v) = paired_complex_vector (fun j => f (v j)).
Proof.
apply: val_inj.
change (exterior_algebra_map (restrict_linear (ComplexScalars.embed R) f)
  (component_val (paired_complex_vector v)) =
  component_val (paired_complex_vector (fun j => f (v j)))).
rewrite !paired_complex_vector_word exterior_algebra_map_word.
congr (exterior_word _).
rewrite map_flatten -map_comp; congr (flatten _); apply: eq_map => j.
change ([:: f (v j); f (ComplexScalars.ii R *: v j)] =
  [:: f (v j); ComplexScalars.ii R *: f (v j)]).
by rewrite linearZ.
Qed.

(** Source for [paired_complex_basis_change]: Federer 1.6.6,
    p. 27, displayed basis-change formula for paired vectors.
    The factor is the real determinant of the complex automorphism. *)
Lemma paired_complex_basis_change (R : realFieldType)
  (V : lmodType (ComplexScalars.C R)) p (v w : 'I_p -> V)
  (hv : is_basis v) (hw : is_basis w) :
  paired_complex_vector w =
  det (real_two_nonzero R) (ordered_real_basisP hv)
    (restrict_linear (ComplexScalars.embed R) (basis_change_map w hv)) *:
  paired_complex_vector v.
Proof.
rewrite -(detE (real_two_nonzero R) (ordered_real_basisP hv)) paired_complex_vector_natural.
congr (paired_complex_vector _); apply: boolp.funext => j.
by rewrite basis_change_mapE.
Qed.

(** Source for [paired_complex_bases_positive_multiple]:
    Federer 1.6.6, p. 27, sign independence. Any two complex bases
    give paired real volumes differing by a strictly positive factor. *)
Theorem paired_complex_bases_positive_multiple (R : realFieldType)
  (V : lmodType (ComplexScalars.C R)) p (v w : 'I_p -> V)
  (hv : is_basis v) (hw : is_basis w) :
  exists d : R, 0 < d /\ paired_complex_vector w = d *: paired_complex_vector v.
Proof.
exists (det (real_two_nonzero R) (ordered_real_basisP hv)
    (restrict_linear (ComplexScalars.embed R) (basis_change_map w hv))).
split; [exact: complex_basis_change_positive | exact: paired_complex_basis_change].
Qed.
