(** Federer (1969), 3.4.5, p. 319: the
    original germ derivatives have bounded symmetric-form
    representatives in every order, with exact operator norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SymmetricForms SymmetricOperatorNorm ContinuousSymmetricFormAdapter
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermJetSymmetry AnalyticGermGrowthUP
  AnalyticGermGrowthSealed AnalyticGermGrowthCover FormalAnalyticJetUP FormalAnalyticJetForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_coefficient_forms_exists]: the
    actual D^m(alpha) used in the metric and the
    Leibniz formula, 3.4.5, p. 319. Only
    proved symmetry and the original growth cover are used;
    no form choice or norm equality is assumed. *)
Theorem analytic_germ_coefficient_forms_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (alpha:analytic_germ_space hNX a):
  exists phi:forall m,S_m X R^o m,
    (forall m t,phi m t=@ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|)
      hNX (@scalar_absolute_value_norm R) [ffun i=>tnth t i] (@AnalyticGermJets.value R X NX hNX a m alpha)) /\
    (forall m,norm_bounded_symmetric_form NX (fun z:R^o=>`|z|) (phi m)) /\
    forall m,symmetric_operator_norm hNX.1 (fun z:R^o=>`|z|) (phi m)=
      (@analytic_germ_jet_norm R X NX hNX a m alpha)%:E.
Proof.
have [s [t [_ [_ hGrowth]]]]:=@analytic_germ_positive_growth_cover R X NX hNX a alpha.
have hFormal:@is_formal_analytic_jet R X NX hNX s t (fun m=>@AnalyticGermJets.value R X NX hNX a m alpha).
  split.
  - move=>m sigma u;exact:(@analytic_germ_jet_symmetric R X NX hNX a m alpha sigma u).
  - exact:((analytic_germ_growth_membership (@AnalyticGermGrowth.laws R X NX hNX a s t) alpha).1 hGrowth).
exact:(@formal_analytic_jet_forms_exists R X NX hNX s t (fun m=>@AnalyticGermJets.value R X NX hNX a m alpha) hFormal).
Qed.
