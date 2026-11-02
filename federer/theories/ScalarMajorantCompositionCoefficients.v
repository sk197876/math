(** Federer (1969), 3.1.24, p. 240: applying the
    exact higher-composition formula to the actual scalar inverse
    and forward majorant identifies the normalized inverse coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormRegularity
  NormClassZeroComposition ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherSymmetricFormUP NormHigherCompositionFormula
  SymmetricForms HomogeneousPolynomialFunctions CompositionFormCoefficient ScalarCompositionCoefficient
  ScalarAffineDifferentials ScalarIdentityForms ScalarCoefficientForms ScalarAnalyticFraction
  ScalarInverseMajorant ScalarInverseMajorantIdentity ScalarForwardMajorantDifferentials ScalarForwardMajorantForms
  NormAnalyticUP NormAnalyticLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_majorant_composition_coefficient_identity]:
    the identity g composed with f equals identity determines
    the scalar inverse coefficients in Federer 3.1.24, p. 240.
    The forms phi are required to be actual derivatives of
    the displayed inverse at zero. Both true composition
    domains are retained; the outer forms are proved actual
    derivatives of the rational majorant. *)
Theorem scalar_majorant_composition_coefficient_identity (R:realType) (b g:R)
    (phi:forall i,S_m R^o R^o i) p :
  0<b -> 0<g -> (1<=p)%N ->
  (forall i,is_norm_higher_differential_form (fun t:R^o=>`|t|)
    (fun j=>@ContinuousMultilinear.evaluation R j R^o R^o (fun t=>`|t|) (fun t=>`|t|)
      (scalar_absolute_value_norm R) (scalar_absolute_value_norm R))
    (fun j=>@ContinuousMultilinear.norm R j R^o R^o (fun t=>`|t|) (fun t=>`|t|)
      (scalar_absolute_value_norm R) (scalar_absolute_value_norm R))
    (scalar_inverse_majorant_domain b) (scalar_inverse_majorant b g) i 0 (phi i)) ->
  sform_polynomial_value (@composition_differential_form_coefficient R R^o R^o R^o p phi
    (fun i=>scalar_coefficient_form i (scalar_forward_majorant_coefficient b g i)) p) 1=
    scalar_affine_derivative_coefficient 1 0 p 0/(p`!)%:R.
Proof.
move=>hb hg hp hphi.
pose N:=fun t:R^o=>`|t|.
pose hN:=scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose ZN i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
pose A:=scalar_inverse_majorant_domain b.
pose B:=scalar_analytic_fraction_domain g.
pose F:=scalar_inverse_majorant b g.
pose G:=scalar_forward_majorant b g.
pose C:=fun x=>A x /\ B (F x).
have hA0:A 0:=scalar_inverse_majorant_zero_domain hb.
have hF0:F 0=0:=scalar_inverse_majorant_zero g hb.
have hB0:B (F 0) by rewrite hF0; exact:scalar_analytic_fraction_zero_domain.
have hFa:@norm_analytic R R^o R^o N N hN hN A F.
  move=>x hx; exact (@scalar_inverse_majorant_analytic_at R b g x hx).
have hFclass:=norm_analytic_class_all_orders hFa.
have hGclass:=(@scalar_forward_majorant_differentials R Z ev ZN hZ b g).1.
have hOpen x (hx:C x):norm_domain_interior N C x.
  exact (@norm_class_zero_composite_interior R R^o R^o R^o N N N A B F G
    (hFclass 0%N).1 (hGclass 0%N).1 x hx).
pose eta:S_m R^o R^o p:=@scalar_coefficient_form R p (@scalar_affine_derivative_coefficient R 1 0 p 0).
have hEtaId:=@scalar_identity_form_actual R Z ev ZN hZ C hOpen p (conj hA0 hB0).
have hEta:is_norm_higher_differential_form N ev ZN C (fun x=>G (F x)) p 0 eta.
  move:hEtaId=>[z [hz he]]; exists z; split; last exact he.
  apply: ((@norm_higher_differential_local_agreement R R^o R^o N N hN hN Z ev ZN hZ
    p C C C (fun x=>1*x+0) (fun x=>G (F x)) hOpen (fun x hx=>iff_refl _) _ 0 (conj hA0 hB0) z).1 hz).
  move=>x hx _; rewrite mul1r addr0; symmetry.
  exact (scalar_majorant_right_inverse hb hg hx.1 hx.2).
have hPsi i (_:(i<=p)%N):is_norm_higher_differential_form N ev ZN B G i (F 0)
    (scalar_coefficient_form i (scalar_forward_majorant_coefficient b g i)).
  rewrite hF0; exact (@scalar_forward_majorant_form_actual R Z ev ZN hZ b g i).
have hpp:(1<=p<=p)%N by rewrite hp leqnn.
have hEq:=@norm_higher_composition_formula R R^o R^o R^o N N N hN hN hN
  Z Z Z ev ZN ev ZN ev ZN hZ hZ hZ A B F G p 0 phi
  (fun i=>scalar_coefficient_form i (scalar_forward_majorant_coefficient b g i)) hp hA0 hB0
  (hFclass p) (hGclass p) (fun i _=>hphi i) hPsi p hpp eta hEta.
rewrite -hEq /eta scalar_coefficient_form_polynomial_unit; reflexivity.
Qed.
