(** Federer (1969), 3.4.12, p. 339: real analyticity of
    the actual original complex reciprocal. Reuse scalar coordinate
    analyticity, the proved real reciprocal and complex reconstruction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm ComplexReciprocalCoordinates NormAnalyticUP NormAnalyticLocal
  NormRegularity NormDifferentialUP NormAnalyticComposition NormAnalyticOperations NormAnalyticConstant NormAnalyticScalarProducts
  ScalarReciprocalAnalytic NormAnalyticComplexCoordinates NormAnalyticComplexSquareModulus
  NormAnalyticComplexReconstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Reciprocals.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable A:X->Prop.
Variable f:X->ComplexScalars.C R.
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation hR:=(@scalar_absolute_value_norm R).
Local Notation B:=(fun x=>A x /\f x!=0).

(** Source for [norm_analytic_complex_reciprocal]: original complex
    reciprocals are analytic on their actual nonzero domain,
    as used in the complex local ring of 3.4.12, p. 339. *)
Theorem norm_analytic_complex_reciprocal:
  @norm_analytic R X CR NX N hNX hN A f ->
  @norm_analytic R X CR NX N hNX hN B (fun x=>(f x)^-1).
Proof.
move=>hF.
have hSquare:=norm_analytic_complex_square_modulus hF.
have hInverse:=@norm_analytic_composition R X R^o R^o NX (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  hNX hR hR A (fun t:R^o=>t!=0) (fun x=>norm_square (f x)) (fun t=>t^-1)
  hSquare (@scalar_reciprocal_analytic R).
have hDomains:(fun x=>A x /\norm_square (f x)!=0)=B.
  apply:funext=>x;by rewrite norm_square_eq0.
rewrite hDomains in hInverse.
have hOpen x (hx:B x):norm_domain_interior NX B x:=
  ((norm_analytic_class_all_orders hInverse 0%N).1 x hx).1.
have hReal:=norm_analytic_complex_real_part hF.
have hImaginary:=norm_analytic_complex_imaginary_part hF.
have hRealB:@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX hR B
    (fun x=>ComplexScalars.re (f x)).
  exact:(@norm_analytic_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX hR A B
    (fun x=>ComplexScalars.re (f x)) (fun x hx=>hx.1) hOpen hReal).
have hImaginaryB:@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX hR B
    (fun x=>ComplexScalars.im (f x)).
  exact:(@norm_analytic_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX hR A B
    (fun x=>ComplexScalars.im (f x)) (fun x hx=>hx.1) hOpen hImaginary).
apply:norm_analytic_complex_reconstruction;first exact:hOpen.
- apply:(norm_analytic_domain_agreement _ (norm_analytic_scalar_product hInverse hRealB))=>x hx.
  exact:esym (complex_reciprocal_real_part hx.2).
- have hNegative:=norm_analytic_subtract
    (@norm_constant_analytic R X R^o NX (fun t:R^o=>`|t|) hNX hR B hOpen 0) hImaginaryB.
  have hNegativeValues:(fun x=>0-ComplexScalars.im (f x))=(fun x=>-ComplexScalars.im (f x)).
    apply:funext=>x;exact:sub0r.
  rewrite hNegativeValues in hNegative.
  apply:(norm_analytic_domain_agreement _ (norm_analytic_scalar_product hInverse hNegative))=>x hx.
  exact:esym (complex_reciprocal_imaginary_part hx.2).
Qed.
End Reciprocals.
