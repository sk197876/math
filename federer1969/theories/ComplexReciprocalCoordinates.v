(** Federer (1969), 3.4.12, p. 339: original complex
    scalar reciprocals in the local holomorphic ring. The
    existing conjugation and squared-modulus laws give the actual
    reciprocal formula; no representation of the sealed field is opened. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ComplexScalarSealed ComplexScalarLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [complex_reciprocal_coordinates]: the local reciprocal
    used in the complex version of the unit argument of
    3.4.7, p. 325, under 3.4.12, p. 339. *)
Lemma complex_reciprocal_coordinates (R:realType) (z:ComplexScalars.C R):
  z!=0 ->z^-1=ComplexScalars.embed R (norm_square z)^-1*conjugate z.
Proof.
move=>hz.
have hSquare:norm_square z!=0 by rewrite norm_square_eq0.
have hConjugate:conjugate z=z^-1*ComplexScalars.embed R (norm_square z).
  by rewrite -mul_conjugate mulrA mulVf // mul1r.
by rewrite hConjugate mulrCA -rmorphM (mulVf hSquare) rmorph1 mulr1.
Qed.

(** Source for [complex_reciprocal_real_part]: exact real coordinate
    of the original inverse, supporting 3.4.12, p. 339. *)
Lemma complex_reciprocal_real_part (R:realType) (z:ComplexScalars.C R):
  z!=0 ->ComplexScalars.re (z^-1)=(norm_square z)^-1*ComplexScalars.re z.
Proof. by move=>hz;rewrite (complex_reciprocal_coordinates hz)
  (ComplexScalarUP.complex_re_scale (ComplexScalars.laws R)) re_conjugate. Qed.

(** Source for [complex_reciprocal_imaginary_part]: exact imaginary
    coordinate of the original inverse, supporting 3.4.12, p. 339. *)
Lemma complex_reciprocal_imaginary_part (R:realType) (z:ComplexScalars.C R):
  z!=0 ->ComplexScalars.im (z^-1)=(norm_square z)^-1*(-ComplexScalars.im z).
Proof. by move=>hz;rewrite (complex_reciprocal_coordinates hz)
  (ComplexScalarUP.complex_im_scale (ComplexScalars.laws R)) im_conjugate. Qed.
