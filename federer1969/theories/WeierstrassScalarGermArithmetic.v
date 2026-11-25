(** Federer (1969), 3.4.6, p. 322: multiplication
    by the original nonzero divided leading coefficient
    and its inverse removes the auxiliary normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity ContinuousMultilinearUP
  ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherDifferentialArithmetic NormHigherDifferentialUnique AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_constant_germ_product]: the
    scalar constants retain their original multiplication in
    the actual germ ring, supporting normalization in
    3.4.6, p. 322. *)
Lemma weierstrass_constant_germ_product (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a (c d:R):
  (@analytic_germ R X NX hNX a (@analytic_constant_representative R X NX hNX a c):
    @analytic_germ_ring R X NX hNX a)*
    analytic_germ (@analytic_constant_representative R X NX hNX a d)=
    analytic_germ (@analytic_constant_representative R X NX hNX a (c*d)).
Proof.
change (@AnalyticGerms.mul R X NX hNX a
  (analytic_germ (@analytic_constant_representative R X NX hNX a c))
  (analytic_germ (@analytic_constant_representative R X NX hNX a d))=
  analytic_germ (@analytic_constant_representative R X NX hNX a (c*d))).
rewrite (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [weierstrass_scalar_germ_jet]: every actual
    higher differential scales by the same original scalar,
    supporting the normalization of 3.4.6, p. 322.
    The proof uses actual derivative fields and representative
    equations, with no coefficient scaling axiom. *)
Lemma weierstrass_scalar_germ_jet (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a m (c:R)
    (alpha:@analytic_germ_ring R X NX hNX a):
  @AnalyticGermJets.value R X NX hNX a m
    ((analytic_germ (@analytic_constant_representative R X NX hNX a c):
      @analytic_germ_ring R X NX hNX a)*alpha)=
    c*:@AnalyticGermJets.value R X NX hNX a m alpha.
Proof.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
have [f hRep]:=@analytic_germ_has_representative R X NX hNX a alpha.
pose F:=analytic_representative_value f.
have [U [b [ha [hUT [hClass _]]]]]:=analytic_representative_analytic f.
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hClass 0%N).1 x hx).1.
have [D [hD _]]:=(hClass m).2.
have hScaled:=@norm_higher_differential_field_scale R X R^o NX N hNX hN Z ev NZ hZ U m F D c hD a ha.
have hFullScaled:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
  m setT U (fun x=>c*:(F x:R^o)) hUT hOpen a ha (c*:D a)).2 hScaled.
have hFull:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
  m setT U F hUT hOpen a ha (D a)).2 (hD a ha).
have hOriginal:=@AnalyticGermJets.laws R X NX hNX a m alpha f hRep.
have hDJet:=@norm_higher_differential_unique R X R^o NX N hNX hN Z ev NZ hZ
  setT F m a _ _ hFull hOriginal.
pose constant:=@analytic_constant_representative R X NX hNX a c.
pose g:=@analytic_multiply_representatives R X NX hNX a constant f.
pose beta:@analytic_germ_ring R X NX hNX a:=(analytic_germ constant:@analytic_germ_ring R X NX hNX a)*alpha.
have hRepG:analytic_germ g=beta.
  rewrite /beta -hRep.
  exact:esym (@analytic_germ_multiply_equation R X NX hNX a _ _ _
    (@AnalyticGerms.laws R X NX hNX a) constant f).
have hNew:=@AnalyticGermJets.laws R X NX hNX a m beta g hRepG.
have hEqual:=@norm_higher_differential_unique R X R^o NX N hNX hN Z ev NZ hZ
  setT (analytic_representative_value g) m a _ _ hNew hFullScaled.
by rewrite hEqual hDJet.
Qed.
