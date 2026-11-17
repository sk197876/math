(** Federer (1969), 3.4.12, p. 339:
    complex-valued real analytic functions are closed under
    their original multiplication. Reuse bounded scalar coordinates,
    real analytic products and actual complex reconstruction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm NormAnalyticUP NormAnalyticOperations
  NormAnalyticScalarProducts NormAnalyticComplexCoordinates NormAnalyticComplexReconstruction
  NormAnalyticLocal NormRegularity NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_complex_product]: actual
    complex multiplication preserves real analyticity, supporting
    the holomorphic local ring of 3.4.12,
    p. 339. No product regularity is assumed. *)
Theorem norm_analytic_complex_product (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop)
    (f g:X->ComplexScalars.C R):
  @norm_analytic R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f ->
  @norm_analytic R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A g ->
  @norm_analytic R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (fun x=>f x*g x).
Proof.
move=>hF hG.
have hOpen a (ha:A a):norm_domain_interior NX A a.
  have hClass:=norm_analytic_class_all_orders hF 0%N.
  exact:(hClass.1 a ha).1.
have hFR:=norm_analytic_complex_real_part hF.
have hFI:=norm_analytic_complex_imaginary_part hF.
have hGR:=norm_analytic_complex_real_part hG.
have hGI:=norm_analytic_complex_imaginary_part hG.
apply:norm_analytic_complex_reconstruction;first exact:hOpen.
- have hReal:=norm_analytic_subtract
    (norm_analytic_scalar_product hFR hGR) (norm_analytic_scalar_product hFI hGI).
  apply:(norm_analytic_domain_agreement _ hReal)=>x hx.
  exact:esym (re_mul (f x) (g x)).
- have hImaginary:=norm_analytic_add
    (norm_analytic_scalar_product hFR hGI) (norm_analytic_scalar_product hFI hGR).
  apply:(norm_analytic_domain_agreement _ hImaginary)=>x hx.
  exact:esym (im_mul (f x) (g x)).
Qed.
