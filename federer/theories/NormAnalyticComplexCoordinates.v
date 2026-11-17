(** Federer (1969), 3.4.12, pp. 338–339:
    the original complex-valued analytic function has real
    analytic real and imaginary coordinates. Reuse their
    actual bounded coordinate maps and real analytic composition. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexCoefficientAlgebra ComplexModulus ComplexScalarNorm ComplexScalarCoordinateBounds
  NormAnalyticUP NormAnalyticBoundedPostcompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable A:X->Prop.
Variable f:X->ComplexScalars.C R.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).

(** Source for [norm_analytic_complex_real_part]: real
    analyticity of the actual original real coordinate,
    supporting 3.4.12, pp. 338–339. *)
Theorem norm_analytic_complex_real_part:
  @norm_analytic R X CR NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f ->
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (fun x=>ComplexScalars.re (f x)).
Proof.
move=>hf;exact:(@norm_analytic_bounded_postcompose R X CR R^o
  NX (@complex_modulus R) (fun t:R^o=>`|t|) hNX (@complex_modulus_real_norm R)
  (@scalar_absolute_value_norm R) A f
  (hom_of_linear (GRing.Linear.clone R CR R^o *:%R (@complex_real_part R) _))
  hf (@complex_real_part_bounded R)).
Qed.

(** Source for [norm_analytic_complex_imaginary_part]: real
    analyticity of the actual original imaginary coordinate,
    supporting 3.4.12, pp. 338–339. *)
Theorem norm_analytic_complex_imaginary_part:
  @norm_analytic R X CR NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f ->
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (fun x=>ComplexScalars.im (f x)).
Proof.
move=>hf;exact:(@norm_analytic_bounded_postcompose R X CR R^o
  NX (@complex_modulus R) (fun t:R^o=>`|t|) hNX (@complex_modulus_real_norm R)
  (@scalar_absolute_value_norm R) A f
  (hom_of_linear (GRing.Linear.clone R CR R^o *:%R (@complex_imaginary_part R) _))
  hf (@complex_imaginary_part_bounded R)).
Qed.
End Coordinates.
