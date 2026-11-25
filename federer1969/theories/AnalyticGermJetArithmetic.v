(** Federer (1969), 3.4.5, p. 319: actual
    germ derivatives respect functional addition and negation.
    This follows from the actual local higher-differential
    arithmetic of 3.1.11, pp. 220–221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherDifferentialUnique NormHigherDifferentialArithmetic NormLinearDomainLaws
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws
  AnalyticGermJetsUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
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
Local Notation G:=(analytic_germ_space hNX a).
Local Notation jet:=(@AnalyticGermJets.value R X NX hNX a).
Local Notation value:=(@analytic_representative_value R X NX hNX a).

(** Source for [analytic_germ_jet_add]: actual D^m
    is additive on the germ ring, 3.4.5, p. 319. *)
Lemma analytic_germ_jet_add m (alpha beta:G):
  jet m (@AnalyticGerms.add R X NX hNX a alpha beta)=jet m alpha+jet m beta.
Proof.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
have [U [c [haU [hUT [hClassF hBoundF]]]]]:=analytic_representative_analytic f.
have [V [d [haV [hVT [hClassG hBoundG]]]]]:=analytic_representative_analytic g.
have [D [hD hDC]]:=(hClassF m).2.
have [E [hE hEC]]:=(hClassG m).2.
pose W:=U `&` V.
have haW:W a by split.
have hOpenU x (hx:U x):norm_domain_interior NX U x:=((hClassF 0%N).1 x hx).1.
have hOpenV x (hx:V x):norm_domain_interior NX V x:=((hClassG 0%N).1 x hx).1.
have hOpenW x (hx:W x):norm_domain_interior NX W x.
  exact:norm_domain_intersection_interior (hOpenU x hx.1) (hOpenV x hx.2).
have hDW x (hx:W x):has_norm_higher_differential NX ev N W (value f) m x (D x).
  exact:((@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev N hZ
    m U W (value f) (fun x hx=>hx.1) hOpenW x hx (D x)).1 (hD x hx.1)).
have hEW x (hx:W x):has_norm_higher_differential NX ev N W (value g) m x (E x).
  exact:((@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev N hZ
    m V W (value g) (fun x hx=>hx.2) hOpenW x hx (E x)).1 (hE x hx.2)).
have hSum:=@norm_higher_differential_field_add R X R^o NX NS hNX hNS Z ev N hZ
  W m (value f) (value g) D E hDW hEW a haW.
have hFullSum:=(@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev N hZ
  m setT W (fun x=>value f x+value g x) (fun x hx=>Logic.I) hOpenW a haW (D a+E a)).2 hSum.
have hFullF:=(@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev N hZ
  m setT U (value f) hUT hOpenU a haU (D a)).2 (hD a haU).
have hFullG:=(@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev N hZ
  m setT V (value g) hVT hOpenV a haV (E a)).2 (hE a haV).
have hJetF:=@AnalyticGermJets.laws R X NX hNX a m alpha f hf.
have hJetG:=@AnalyticGermJets.laws R X NX hNX a m beta g hg.
have hEqualF:=@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev N hZ
  setT (value f) m a _ _ hFullF hJetF.
have hEqualG:=@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev N hZ
  setT (value g) m a _ _ hFullG hJetG.
have hRep:@analytic_germ R X NX hNX a (@analytic_add_representatives R X NX hNX a f g)=
    @AnalyticGerms.add R X NX hNX a alpha beta.
  by rewrite -hf -hg (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
have hJet:=@AnalyticGermJets.laws R X NX hNX a m _ _ hRep.
have hEqual:=@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev N hZ
  setT (fun x=>value f x+value g x) m a _ _ hJet hFullSum.
by rewrite hEqual hEqualF hEqualG.
Qed.
End Arithmetic.
