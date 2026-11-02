(** Federer (1969), 1.8.2, p. 39, Cauchy's inequality: the absolute value of
    a complex scalar is the nonnegative square root of the sum of its
    squared real and imaginary parts. This specifies scalar background used
    by the displayed inequality. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarSealed ComplexScalarLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [is_complex_modulus]: Federer 1.8.2,
    p. 39, supporting abstract specification of |z| by its sign
    and square. Existence is supplied separately behind a seal. *)
Record is_complex_modulus (R : realFieldType) (z : ComplexScalars.C R) (r : R) : Prop := {
  complex_modulus_nonnegative : 0 <= r;
  complex_modulus_square : r^+2 = norm_square z
}.

(** Source for [complex_modulus_unique]: Federer 1.8.2,
    p. 39, supporting uniqueness of a complex absolute value. *)
Theorem complex_modulus_unique (R : realFieldType) (z : ComplexScalars.C R) a b :
  is_complex_modulus z a -> is_complex_modulus z b -> a = b.
Proof.
move=> [ha has] [hb hbs]; apply/eqP; rewrite eq_le; apply/andP; split.
- by rewrite -(ler_sqr ha hb) has hbs.
- by rewrite -(ler_sqr hb ha) has hbs.
Qed.

(** Source for [complex_modulus_zero_iff]: Federer 1.8.2,
    p. 39, supporting definiteness of the complex absolute value. *)
Theorem complex_modulus_zero_iff (R : realFieldType) (z : ComplexScalars.C R) r :
  is_complex_modulus z r -> (r == 0) = (z == 0).
Proof.
move=> [hr hs]; by rewrite -norm_square_eq0 -hs expf_eq0.
Qed.
