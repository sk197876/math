(** Federer (1969), 1.8.2, p. 39: private existence witness for the absolute
    value of a complex scalar. Mathematical clients use ComplexModulusUP and
    the sealed interface. Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarSealed ComplexScalarLaws ComplexModulusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [complex_modulus_exists]: Federer 1.8.2,
    p. 39, supporting existence of the nonnegative scalar modulus. *)
Theorem complex_modulus_exists (R : rcfType) (z : ComplexScalars.C R) :
  exists r : R, is_complex_modulus z r.
Proof.
exists (Num.sqrt (norm_square z)); constructor; first exact: sqrtr_ge0.
by rewrite sqr_sqrtr // norm_square_ge0.
Qed.
