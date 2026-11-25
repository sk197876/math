(** Federer (1969), 3.2.13, p. 250: the
    product x^s exp(-x) has derivative
    s exp(-x)x^(s-1)-exp(-x)x^s on x>0.
    This is the integration-by-parts input for
    Gamma(s+1)=s Gamma(s), using the internal calculus only. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import Hom RealNormUP EulerGammaUP RealPower RealPowerDifferential
  RealExponentialSealed RealExponentialDifferential NormDifferentialUP NormDifferentialArithmetic
  NormDifferentialLocal NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra ScalarHornerDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_gamma_primitive]: the product
    x^s exp(-x) whose endpoint terms vanish
    in the Gamma recurrence, Federer 3.2.13, p. 250.
    Only positive x is used by the differential theorem. *)
Definition euler_gamma_primitive (R:realType) (s x:R):R:=
  real_power x s*RealExponential.exponential (-x).

(** Source for [euler_gamma_primitive_derivative]: the
    derivative of x^s exp(-x) in the
    recurrence calculation, Federer 3.2.13, p. 250. *)
Definition euler_gamma_primitive_derivative (R:realType) (s x:R):R:=
  s*euler_gamma_integrand s x-euler_gamma_integrand (s+1) x.

(** Source for [euler_gamma_primitive_differential]: actual
    first derivative for the integration-by-parts proof
    of Gamma(s+1)=s Gamma(s), Federer 3.2.13, p. 250.
    This supporting differential is valid for every
    real s at each positive x. *)
Lemma euler_gamma_primitive_differential (R:realType) (s a:R):
  0<a ->has_norm_differential (fun r:R^o=>`|r|) (fun r:R^o=>`|r|) setT
    (euler_gamma_primitive s) a
    (@scalar_coefficient_linear_map R R^o (euler_gamma_primitive_derivative s a)).
Proof.
move=>ha; pose hN:=@scalar_absolute_value_norm R.
have hWhole:norm_domain_interior (fun r:R^o=>`|r|) setT a.
  exists 1; split; first exact:ltr01; by move=>h hh.
have hId:=@scalar_identity_coefficient_differential R setT a hWhole.
have hNeg:=@norm_differential_scale R R^o R^o _ _ hN hN setT (fun x=>x) a
  (@scalar_coefficient_linear_map R R^o 1) (-1) hId.
have hFun:(fun x:R^o=>(-1)*:x)=(fun x:R^o=>(-x:R^o)).
  apply:funext=>x; change ((-1)*x= -x); exact:mulN1r.
have hTerm:(-1)*:@scalar_coefficient_linear_map R R^o 1=
    @scalar_coefficient_linear_map R R^o (-1).
  apply:hom_ext=>x; change (-1*(x*1)=x*(-1)); ring.
rewrite hFun hTerm in hNeg.
have hExp:=@real_exponential_differential R (-a).
have hExpTerm:real_exponential_linear_term (-a)=
    @scalar_coefficient_linear_map R R^o (RealExponential.exponential (-a)).
  apply:hom_ext=>x; change (RealExponential.exponential (-a)*x=x*RealExponential.exponential (-a)); ring.
rewrite hExpTerm in hExp.
have hNegExp:=norm_curve_chain_on_domain hN (fun x (_:setT x)=>Logic.I) hNeg hExp.
have hNegValue:(-1)*:(RealExponential.exponential (-a):R^o)= -RealExponential.exponential (-a).
  change (-1*RealExponential.exponential (-a)= -RealExponential.exponential (-a)); exact:mulN1r.
rewrite hNegValue in hNegExp.
have hPow:=@real_power_differential R s a ha.
have hPowTerm:real_power_linear_term s a=
    @scalar_coefficient_linear_map R R^o (s*real_power a (s-1)).
  apply:hom_ext=>x; change ((s*real_power a (s-1))*x=x*(s*real_power a (s-1))); ring.
rewrite hPowTerm in hPow.
have hProd:=norm_curve_scalar_product hN hPow hNegExp.
have hCoefficient:(s*real_power a (s-1))*:(RealExponential.exponential (-a):R^o)+
    real_power a s*:(-RealExponential.exponential (-a):R^o)=euler_gamma_primitive_derivative s a.
  change ((s*real_power a (s-1))*RealExponential.exponential (-a)+
    real_power a s*(-RealExponential.exponential (-a))=
    s*euler_gamma_integrand s a-euler_gamma_integrand (s+1) a).
  rewrite /euler_gamma_integrand addrK; ring.
rewrite hCoefficient in hProd; exact hProd.
Qed.
