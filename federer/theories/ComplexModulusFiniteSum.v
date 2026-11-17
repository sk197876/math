(** Federer (1969), 3.4.12, p. 339:
    the complex coefficient bounds in 3.4.6 use the
    existing finite norm-sum and triangle laws. These
    are direct connections to the original scalar modulus. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_modulus_finite_sum]: bound the
    original finite complex coefficient sums, 3.4.12,
    p. 339, adapting 3.4.6, p. 324. *)
Theorem complex_modulus_finite_sum (R:realType) (I:finType)
    (f:I->ComplexScalars.C R):
  complex_modulus (\sum_i f i)<=\sum_i complex_modulus (f i).
Proof.
exact:(@real_seminorm_sum R (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  (@complex_modulus R) (@complex_modulus_real_norm R).1 I f).
Qed.

(** Source for [complex_modulus_subtract_bound]: bound
    the original complex coefficient subtractions, 3.4.12,
    p. 339, adapting 3.4.6, p. 324. *)
Theorem complex_modulus_subtract_bound (R:realType) (z w:ComplexScalars.C R):
  complex_modulus (z-w)<=complex_modulus z+complex_modulus w.
Proof.
have h:=@real_seminorm_triangle R
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  (@complex_modulus R) (@complex_modulus_real_norm R).1 z (-w).
by rewrite (real_seminorm_negate (@complex_modulus_real_norm R).1) in h.
Qed.
