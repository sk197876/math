(** Federer (1969), 3.4.12, pp. 338–339:
    the original complex scalar target has its usual
    Hermitian product. Reuse conjugation and the squared
    modulus laws of 1.6.6 and 1.8.2, pp. 26–27, 39. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexScalarUP
  ComplexScalarLaws ComplexCoefficientAlgebra HermitianUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [complex_scalar_hermitian]: the usual
    scalar Hermitian product used for complex-valued holomorphic
    functions in 3.4.12, pp. 338–339. *)
Definition complex_scalar_hermitian (R:realFieldType)
    (z w:(ComplexScalars.C R)^o):ComplexScalars.C R:=conjugate z*w.

(** Source for [complex_scalar_hermitian_laws]: the original
    scalar product satisfies all independent Hermitian laws,
    including positivity, as required in 3.4.12,
    pp. 338–339; apply the existing scalar identities. *)
Theorem complex_scalar_hermitian_laws (R:realFieldType):
  @is_hermitian_product R (ComplexScalars.C R)^o (@complex_scalar_hermitian R).
Proof.
constructor.
- split=>x a y z;rewrite /complex_scalar_hermitian.
  + change (conjugate (ComplexScalars.embed R a*y+z)*x=
      ComplexScalars.embed R a*(conjugate y*x)+conjugate z*x).
    by rewrite conjugate_add conjugate_scale mulrDl mulrA.
  + change (conjugate x*(ComplexScalars.embed R a*y+z)=
      ComplexScalars.embed R a*(conjugate x*y)+conjugate x*z).
    by rewrite mulrDr mulrCA.
- move=>z w;change (conjugate z*(ComplexScalars.ii R*w)=
    ComplexScalars.ii R*(conjugate z*w)).
  by rewrite mulrCA.
- move=>z w;by rewrite /complex_scalar_hermitian conjugate_mul conjugateK mulrC.
- move=>z hz;rewrite /complex_scalar_hermitian mulrC mul_conjugate re_embed.
  exact:norm_square_gt0 hz.
Qed.
