(** Federer (1969), 3.4.12, pp. 338–339:
    real and imaginary scalar coordinates are bounded
    maps for the original complex absolute value. These
    connections reuse the exact squared-modulus formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexCoefficientAlgebra ComplexModulus NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Bounds.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).

(** Source for [complex_modulus_real_part_bound]: the
    original real coordinate has absolute value at most
    the complex absolute value, supporting 3.4.12,
    pp. 338–339. *)
Lemma complex_modulus_real_part_bound (z:C):`|ComplexScalars.re z|<=complex_modulus z.
Proof.
rewrite -(ler_sqr (normr_ge0 _) (complex_modulus_ge0 _)) -normrX
  ger0_norm ?sqr_ge0 // complex_modulus_sqr /norm_square.
by rewrite lerDl sqr_ge0.
Qed.

(** Source for [complex_modulus_imaginary_part_bound]: the
    original imaginary coordinate has absolute value at most
    the complex absolute value, supporting 3.4.12,
    pp. 338–339. *)
Lemma complex_modulus_imaginary_part_bound (z:C):`|ComplexScalars.im z|<=complex_modulus z.
Proof.
rewrite -(ler_sqr (normr_ge0 _) (complex_modulus_ge0 _)) -normrX
  ger0_norm ?sqr_ge0 // complex_modulus_sqr /norm_square.
by rewrite lerDr sqr_ge0.
Qed.

(** Source for [complex_real_part_bounded]: boundedness of
    the actual real coordinate functional used in the
    complex-to-real analytic comparison of 3.4.12, pp. 338–339. *)
Theorem complex_real_part_bounded:
  @norm_bounded_linear R CR R^o (@complex_modulus R) (fun r:R^o=>`|r|)
    (hom_of_linear (GRing.Linear.clone R CR R^o *:%R (@complex_real_part R) _)).
Proof.
exists 1;split;first exact:ler01.
move=>z;rewrite mul1r;exact:complex_modulus_real_part_bound.
Qed.

(** Source for [complex_imaginary_part_bounded]: boundedness of
    the actual imaginary coordinate functional used in the
    complex-to-real analytic comparison of 3.4.12, pp. 338–339. *)
Theorem complex_imaginary_part_bounded:
  @norm_bounded_linear R CR R^o (@complex_modulus R) (fun r:R^o=>`|r|)
    (hom_of_linear (GRing.Linear.clone R CR R^o *:%R (@complex_imaginary_part R) _)).
Proof.
exists 1;split;first exact:ler01.
move=>z;rewrite mul1r;exact:complex_modulus_imaginary_part_bound.
Qed.
End Bounds.
