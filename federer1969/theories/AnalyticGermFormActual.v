(** Federer (1969), 3.4.5, p. 319: actual
    coefficient forms of a germ are the actual higher
    differentials of every original representative on every
    neighbourhood of its centre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherSymmetricFormUP SymmetricForms
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_coefficient_actual_on_neighbourhood]:
    actual D^m(alpha) and its representative equation in
    3.4.5, p. 319, localized to any original
    open neighbourhood for the Leibniz formula. *)
Theorem analytic_germ_coefficient_actual_on_neighbourhood (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m
    (alpha:analytic_germ_space hNX a) (f:@analytic_representative_type R X NX hNX a)
    (U:set X) (phi:S_m X R^o m):
  analytic_germ f=alpha ->U a ->(forall x,U x ->norm_domain_interior NX U x) ->
  (forall t,phi t=@ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|)
    hNX (@scalar_absolute_value_norm R) [ffun i=>tnth t i] (@AnalyticGermJets.value R X NX hNX a m alpha)) ->
  is_norm_higher_differential_form NX
    (fun i=>@ContinuousMultilinear.evaluation R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
    (fun i=>@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
    U (analytic_representative_value f) m a phi.
Proof.
move=>hf ha hOpen hPhi.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NS hNX hNS.
pose N i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS.
pose z:=@AnalyticGermJets.value R X NX hNX a m alpha.
exists z;split.
- exact:((@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev N hZ
    m setT U (analytic_representative_value f) (fun x hx=>Logic.I) hOpen a ha z).1
      (@AnalyticGermJets.laws R X NX hNX a m alpha f hf)).
- move=>u;rewrite hPhi.
  congr ((ev m) _ z);apply/ffunP=>i;by rewrite ffunE tnth_mktuple.
Qed.
