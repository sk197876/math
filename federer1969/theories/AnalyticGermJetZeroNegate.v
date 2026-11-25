(** Federer (1969), 3.4.5, p. 319: the
    actual germ derivatives send zero to zero and commute
    with negation, supporting continuity of the ring operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialConstant
  NormHigherDifferentialUnique AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed
  AnalyticGermRingLaws AnalyticGermJetsUP AnalyticGermJetsSealed AnalyticGermJetArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Arithmetic.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation NS:=(fun z:R^o=>`|z|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X R^o NX NS hNX hNS).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX NS hNX hNS).
Local Notation N:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS).
Local Notation jet:=(@AnalyticGermJets.value R X NX hNX a).

(** Source for [analytic_germ_jet_zero]: every order
    of the actual zero germ is zero, 3.4.5, p. 319. *)
Lemma analytic_germ_jet_zero m:jet m (@analytic_germ_zero R X NX hNX a)=0.
Proof.
have hForm:@constant_higher_form R Z 0 m=0 by case:m.
have hZero:@ev 0%N [ffun i:'I_0=>(0:X)] 0=0 by rewrite linear0.
have hActual:=@norm_higher_differential_constant R X R^o NX NS hNX hNS Z ev N hZ setT
  (fun x _=>norm_full_domain_interior NX x) 0 0 hZero m a Logic.I.
have hJet:=@AnalyticGermJets.laws R X NX hNX a m (@analytic_germ_zero R X NX hNX a)
  (@analytic_constant_representative R X NX hNX a 0) (erefl _).
have hEqual:=@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev N hZ
  setT (fun _=>0) m a _ _ hJet hActual.
by rewrite hEqual hForm.
Qed.

(** Source for [analytic_germ_jet_negate]: every original
    germ derivative commutes with functional negation, 3.4.5, p. 319. *)
Lemma analytic_germ_jet_negate m (alpha:analytic_germ_space hNX a):
  jet m (@AnalyticGerms.opp R X NX hNX a alpha)=-(jet m alpha).
Proof.
have hAdd:=@analytic_germ_jet_add R X NX hNX a m (@AnalyticGerms.opp R X NX hNX a alpha) alpha.
rewrite analytic_germ_add_negate analytic_germ_jet_zero in hAdd.
apply/eqP;by rewrite -addr_eq0 -hAdd eqxx.
Qed.
End Arithmetic.
