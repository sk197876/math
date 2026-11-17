(** Federer (1969), 3.4.12, pp. 338–339:
    real analytic scalar coordinates reconstruct the actual
    original complex-valued analytic function. Reuse the finite
    analytic synthesis theorem and original scalar decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarUP
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormAnalyticUP
  NormAnalyticFiniteSynthesis NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_complex_reconstruction]: the
    actual real and imaginary analytic coordinates give
    the original complex-valued analytic function, supporting
    3.4.12, pp. 338–339. Its scalar norm
    remains the original absolute value. *)
Theorem norm_analytic_complex_reconstruction (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop) (f:X->ComplexScalars.C R):
  (forall a,A a ->norm_domain_interior NX A a) ->
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (fun x=>ComplexScalars.re (f x)) ->
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (fun x=>ComplexScalars.im (f x)) ->
  @norm_analytic R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f.
Proof.
move=>hA hReal hImaginary.
pose v (i:bool):restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o:=
  if i then ComplexScalars.ii R else 1.
pose g (i:bool):X->R:=if i then (fun x=>ComplexScalars.im (f x)) else
  (fun x=>ComplexScalars.re (f x)).
have hG i:@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) A (g i).
  by case:i;[exact:hImaginary|exact:hReal].
have hSum:=@norm_analytic_finite_synthesis R X
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A bool v g hA hG.
apply:(norm_analytic_domain_agreement _ hSum)=>x hx.
rewrite big_bool /v /g.
change (ComplexScalars.embed R (ComplexScalars.im (f x))*ComplexScalars.ii R+
  ComplexScalars.embed R (ComplexScalars.re (f x))*1=f x).
by rewrite mulr1 mulrC addrC -(complex_decomposition (ComplexScalars.laws R)).
Qed.
