(** Federer (1969), 3.4.12, pp. 338–339: complex
    linearity of a real map follows from commutation with
    the original imaginary unit. Reuse the sealed scalar
    decomposition of 1.6.6, p. 26. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom ScalarRestriction ComplexScalarUP ComplexScalarSealed ComplexRealLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_scalar_real_expansion]: expand the original
    complex scalar action into its two real actions, supporting
    3.4.12, pp. 338–339, by 1.6.6, p. 26. *)
Lemma complex_scalar_real_expansion (R:realFieldType) (X:lmodType (ComplexScalars.C R))
    (c:ComplexScalars.C R) (x:X):
  c*:x=ComplexScalars.embed R (ComplexScalars.re c)*:x+
    ComplexScalars.embed R (ComplexScalars.im c)*:(ComplexScalars.ii R*:x).
Proof.
rewrite scalerA [ComplexScalars.embed R _*ComplexScalars.ii R]mulrC -scalerDl.
by rewrite -(complex_decomposition (ComplexScalars.laws R)).
Qed.

(** Source for [complex_real_linear_imaginary_criterion]: the original
    additional first-differential law of 3.4.12, p. 338,
    follows from its imaginary-unit special case and real linearity. *)
Theorem complex_real_linear_imaginary_criterion (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R))
    (L:Hom (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y)):
  (forall x,L (ComplexScalars.ii R*:x)=ComplexScalars.ii R*:(L x:Y)) ->
  is_complex_linear_real_map L.
Proof.
move=>hI c x.
have hReal (r:R) (z:X):L (ComplexScalars.embed R r*:z)=ComplexScalars.embed R r*:(L z:Y).
  change (L (r*:(z:restricted_space (ComplexScalars.embed R) X))=
    (r*:(L z:restricted_space (ComplexScalars.embed R) Y):restricted_space (ComplexScalars.embed R) Y)).
  by rewrite linearZ.
have hAdd y z:L (y+z)=L y+L z:=linearD L y z.
rewrite (complex_scalar_real_expansion c x) hAdd !hReal hI.
exact:esym (complex_scalar_real_expansion c (L x:Y)).
Qed.
