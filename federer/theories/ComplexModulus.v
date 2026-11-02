(** Federer (1969), 1.8.2, p. 39: public complex modulus and elementary laws
    needed to choose a unit phase. All proofs use the sealed modulus
    specification and scalar laws. Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarSealed ComplexScalarUP ComplexScalarLaws
  ComplexModulusUP ComplexModulusSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Modulus.
Variable R : rcfType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).

(** Source for [complex_modulus]: Federer 1.8.2, p. 39,
    |z| supplied by its abstract nonnegative-square laws. *)
Definition complex_modulus (z : C) : R := @ComplexModulus.norm R z.

(** Source for [complex_modulusP]: Federer 1.8.2, p. 39,
    the public absolute value satisfies its defining specification. *)
Theorem complex_modulusP z : is_complex_modulus z (complex_modulus z).
Proof. exact: ComplexModulus.laws. Qed.

(** Source for [complex_modulus_ge0]: Federer 1.8.2, p. 39,
    supporting nonnegativity of complex absolute values. *)
Lemma complex_modulus_ge0 z : 0 <= complex_modulus z.
Proof. exact: complex_modulus_nonnegative (complex_modulusP z). Qed.

(** Source for [complex_modulus_sqr]: Federer 1.8.2, p. 39,
    supporting square identity for the absolute value. *)
Lemma complex_modulus_sqr z : (complex_modulus z)^+2 = norm_square z.
Proof. exact: complex_modulus_square (complex_modulusP z). Qed.

(** Source for [complex_modulus_eq0]: Federer 1.8.2, p. 39,
    supporting definiteness needed when normalizing a nonzero scalar. *)
Lemma complex_modulus_eq0 z : (complex_modulus z == 0) = (z == 0).
Proof. exact: complex_modulus_zero_iff (complex_modulusP z). Qed.

(** Source for [complex_modulus_gt0]: Federer 1.8.2, p. 39,
    a nonzero complex scalar has positive absolute value. *)
Lemma complex_modulus_gt0 z : z != 0 -> 0 < complex_modulus z.
Proof. by move=> hz; rewrite lt0r complex_modulus_eq0 hz complex_modulus_ge0. Qed.

(** Source for [complex_modulus_real]: Federer 1.8.2, p. 39,
    supporting compatibility with the absolute value of a real scalar. *)
Theorem complex_modulus_real a : complex_modulus (embed a) = `|a|.
Proof.
apply: (complex_modulus_unique (complex_modulusP _)); constructor; first exact: normr_ge0.
by rewrite /norm_square re_embed im_embed expr0n addr0 -normrX (ger0_norm (sqr_ge0 a)).
Qed.

(** Source for [complex_norm_square_mul]: Federer 1.8.2,
    p. 39, supporting multiplicativity of squared complex absolute values. *)
Lemma complex_norm_square_mul (z w : C) : norm_square (z*w) = norm_square z * norm_square w.
Proof.
apply: (fmorph_inj embed).
rewrite rmorphM -!mul_conjugate conjugate_mul.
by rewrite !mulrA [z*w*conjugate z]mulrAC.
Qed.

(** Source for [complex_modulus_mul]: Federer 1.8.2, p. 39,
    supporting multiplicativity used in the unit-phase argument. *)
Theorem complex_modulus_mul z w :
  complex_modulus (z*w) = complex_modulus z * complex_modulus w.
Proof.
apply: (complex_modulus_unique (complex_modulusP _)); constructor.
- exact: mulr_ge0 (complex_modulus_ge0 z) (complex_modulus_ge0 w).
- by rewrite exprMn !complex_modulus_sqr complex_norm_square_mul.
Qed.
End Modulus.
