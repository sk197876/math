(** Federer (1969), 3.1.24, p. 239: compute
    the composition coefficient through the actual scalar rational
    composite, exactly as in the printed special case. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom Bilinear RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SymmetricForms HomogeneousPolynomialFunctions NormHigherSymmetricFormUP NormHigherCompositionFormula
  CompositionFormCoefficient ScalarAnalyticFraction ScalarAnalyticFractionDifferentials
  ScalarAnalyticFractionForms ScalarAnalyticFractionPolynomial ScalarAnalyticCompositionForm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_analytic_composition_coefficient]: the
    scalar special-case computation justifying the value of the
    sum over S(p) in Federer 3.1.24, p. 239.
    Apply the already proved exact higher-composition formula
    to x/(1-x) and gamma y/(1-gamma y), then evaluate
    the actual derivative of their simplified composite. The
    result is gamma(gamma+1)^(p-1), including gamma=0. *)
Theorem scalar_analytic_composition_coefficient (R:realType) (g:R) p :
  0<=g -> (1<=p)%N ->
  sform_polynomial_value (@composition_differential_form_coefficient R R^o R^o R^o p
    (fun i=>scalar_analytic_fraction_form (1:R) i)
    (fun i=>scalar_analytic_fraction_form g i) p) 1= g*(g+1)^+(p-1).
Proof.
move=>hg hp.
pose N:=fun x:R^o=>`|x|.
have hN:=scalar_absolute_value_norm R.
pose Z:=fun i=>@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev:=fun i=>@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose ZN:=fun i=>@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ:=fun i=>@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
have [hf _]:=scalar_analytic_fraction_differentials hZ (1:R).
have [hgReg _]:=scalar_analytic_fraction_differentials hZ g.
pose eta:=(g/(g+1))*:scalar_analytic_fraction_form (g+1) p.
have hEta:=@scalar_analytic_composition_form_actual R Z ev ZN hZ g p hg hp.
have ha:=scalar_analytic_fraction_zero_domain (1:R).
have hb:scalar_analytic_fraction_domain g (scalar_analytic_fraction 1 0).
  rewrite scalar_analytic_fraction_zero; exact: scalar_analytic_fraction_zero_domain.
have hfp i (_:(i<=p)%N):is_norm_higher_differential_form N ev ZN
    (scalar_analytic_fraction_domain 1) (scalar_analytic_fraction 1) i 0
    (scalar_analytic_fraction_form 1 i).
  exact: scalar_analytic_fraction_form_actual hZ 1 i.
have hgp i (_:(i<=p)%N):is_norm_higher_differential_form N ev ZN
    (scalar_analytic_fraction_domain g) (scalar_analytic_fraction g) i (scalar_analytic_fraction 1 0)
    (scalar_analytic_fraction_form g i).
  rewrite scalar_analytic_fraction_zero; exact: scalar_analytic_fraction_form_actual hZ g i.
have hpp:(1<=p<=p)%N by rewrite hp leqnn.
have heq:=@norm_higher_composition_formula R R^o R^o R^o N N N hN hN hN
  Z Z Z ev ZN ev ZN ev ZN hZ hZ hZ
  (scalar_analytic_fraction_domain 1) (scalar_analytic_fraction_domain g)
  (scalar_analytic_fraction 1) (scalar_analytic_fraction g) p 0
  (fun i=>scalar_analytic_fraction_form 1 i) (fun i=>scalar_analytic_fraction_form g i)
  hp ha hb (hf p) (hgReg p) hfp hgp p hpp eta hEta.
have heval:sform_polynomial_value eta 1=
    (g/(g+1))*sform_polynomial_value (scalar_analytic_fraction_form (g+1) p) 1.
  have hh:=linZ (@sform_polynomial_linear R R^o R^o p) (g/(g+1))
    (scalar_analytic_fraction_form (g+1) p).
  exact (congr1 (fun F:R^o->R^o=>F 1) hh).
rewrite -heq heval (scalar_analytic_fraction_polynomial_unit (g+1) hp).
have hgne:g+1!=0 by apply: lt0r_neq0; lra.
have hpe:p= (p-1).+1 by rewrite subn1 prednK.
have hpow:(g+1)^+p= (g+1)*(g+1)^+(p-1) by rewrite -exprS -hpe.
rewrite hpow.
field; exact hgne.
Qed.
