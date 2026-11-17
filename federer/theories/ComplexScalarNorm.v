(** Federer (1969), 3.4.12, pp. 338–339:
    the original complex absolute value is the norm
    of the scalar target. Identify it with the
    existing Hermitian inner norm through its square laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexModulus
  ComplexScalarHermitian HermitianRealImaginary HermitianComplexNorm
  ComplexNormUP InnerNorm HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Norm.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hH:=(@complex_scalar_hermitian_laws R).
Local Notation hB:=(hermitian_real_inner_product hH).

(** Source for [complex_scalar_inner_norm]: the existing
    Hermitian norm equals the original complex absolute value,
    supporting 3.4.12, pp. 338–339. *)
Lemma complex_scalar_inner_norm (z:C):inner_norm hB z=complex_modulus z.
Proof.
apply:inner_norm_value;first exact:complex_modulus_ge0.
by rewrite complex_modulus_sqr /hermitian_real_part /complex_scalar_hermitian
  mulrC mul_conjugate re_embed.
Qed.

(** Source for [complex_modulus_real_norm]: the complex
    scalar target's original absolute value is a real
    norm on the underlying real space, 3.4.12,
    pp. 338–339. No scalar metric is replaced. *)
Theorem complex_modulus_real_norm:is_real_norm (fun z:CR=>complex_modulus z).
Proof.
have hEqual:(fun z:CR=>inner_norm hB z)=(fun z:CR=>complex_modulus z).
  apply:funext=>z;exact:complex_scalar_inner_norm.
rewrite -hEqual;exact:inner_norm_real_norm.
Qed.

(** Source for [complex_modulus_complex_norm]: the original
    complex scalar norm satisfies exact complex homogeneity,
    3.4.12, pp. 338–339. *)
Theorem complex_modulus_complex_norm:@is_complex_norm R C^o (@complex_modulus R).
Proof.
constructor;first exact:complex_modulus_real_norm.
move=>c z;change (complex_modulus (c*z)=complex_modulus c*complex_modulus z).
exact:complex_modulus_mul.
Qed.
End Norm.
