(** Federer (1969), 3.4.5, pp. 318–321: finite
    actual jets of divided directional coefficient fields.
    This supporting rule uses the actual D^q D^p
    grouping identity of 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticDomain NormAnalyticOperations
  NormAnalyticHigherJet NormFiniteJetAgreement NormFiniteJetAgreementOperations
  NormFiniteJetDerivativeAgreement NormFiniteJetLinearPostcompose AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CoefficientAgreement.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).
Local Notation AN A f:=(@norm_analytic R X Y NX NY hNX hNY A f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X Y NX NY hNX hNY).

(** Source for [analytic_directional_coefficient_unique]: any
    fields satisfying the original coefficient equations agree
    throughout the original analytic domain, supporting 3.4.5,
    pp. 318–321. No values outside that domain are compared. *)
Lemma analytic_directional_coefficient_unique (A:set X) (f:X->Y) k v (c d:X->Y):
  AN A f ->Coefficient A f k v c ->Coefficient A f k v d ->
  forall x,A x ->c x=d x.
Proof.
move=>hf hc hd x hx.
have [F [hF hAnalyticF]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY k A f hf.
by rewrite (hc x hx (F x) (hF x hx)) (hd x hx (F x) (hF x hx)).
Qed.

(** Source for [analytic_directional_coefficient_analytic]: every
    original coefficient field, independently specified by actual
    derivative equations, is analytic on its original domain,
    supporting 3.4.5, pp. 318–321. *)
Lemma analytic_directional_coefficient_analytic (A:set X) (f:X->Y) k v (c:X->Y):
  AN A f ->Coefficient A f k v c ->AN A c.
Proof.
move=>hf hc;have [d [hd hAnalyticD]]:=@analytic_directional_coefficient_exists R X Y NX NY hNX hNY A f k v hf.
apply:(norm_analytic_domain_agreement _ hAnalyticD)=>x hx.
exact:(@analytic_directional_coefficient_unique A f k v d c hf hd hc x hx).
Qed.

(** Source for [analytic_directional_coefficient_finite_jet_agreement]:
    actual pth divided directional coefficient fields retain
    q finite agreeing jets whenever the original functions
    have p+q agreeing jets. The direction and original
    domains are retained, supporting 3.4.5, pp. 318–321. *)
Theorem analytic_directional_coefficient_finite_jet_agreement (A B:set X) (f g:X->Y)
    p q a v (c d:X->Y):
  A a ->B a ->AN A f ->AN B g ->
  Coefficient A f p v c ->Coefficient B g p v d ->
  norm_finite_jet_agreement NX ev NZ A B f g (p+q)%N a ->
  norm_finite_jet_agreement NX ev NZ A B c d q a.
Proof.
move=>ha hb hf hg hc hd hAgree.
have [F [hF hAnalyticF]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY p A f hf.
have [G [hG hAnalyticG]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY p B g hg.
pose hNP:=continuous_multilinear_norm_is_norm hNY (hZ p).
pose L:Hom (Z p) Y:=((p`!)%:R)^-1*:(ev p [ffun _:'I_p=>v]).
have hEval:norm_bounded_linear (NZ p) NY (ev p [ffun _:'I_p=>v]).
  exists (\prod_(i<p) NX v);split.
  - apply:prodr_ge0=>i _;exact:(real_seminorm_nonnegative hNX.1 v).
  - move=>z;rewrite mulrC.
    have hBound:=multilinear_operator_bound (continuous_multilinear_norm_laws (hZ p) z) [ffun _:'I_p=>v].
    have hProduct:(\prod_(i<p) NX ([ffun _: 'I_p=>v] i))=\prod_(i<p) NX v.
      by apply:eq_bigr=>i _;rewrite ffunE.
    by rewrite hProduct in hBound.
have hL:norm_bounded_linear (NZ p) NY L:=norm_bounded_linear_scale hNY _ hEval.
have hDerivativeAgree:=@norm_finite_jet_derivative_agreement R X Y NX NY hNX hNY p A B f g
  F G q a hF hG hAgree.
have hEvaluationAgree:=@norm_finite_jet_linear_postcompose R X (Z p) Y NX (NZ p) NY hNX hNP hNY
  A B F G q a L ha hb hAnalyticF hAnalyticG hL hDerivativeAgree.
have hCA x (hx:A x):c x=L (F x).
  by rewrite (hc x hx (F x) (hF x hx)) /L hom_scaleE.
have hDB x (hx:B x):d x=L (G x).
  by rewrite (hd x hx (G x) (hG x hx)) /L hom_scaleE.
have hOpenA x (hx:A x):norm_domain_interior NX A x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have hOpenB x (hx:B x):norm_domain_interior NX B x:=
  ((norm_analytic_class_all_orders hg 0%N).1 x hx).1.
have hFirst:=@norm_finite_jet_agreement_local R X Y NX NY hNX hNY Z ev NZ hZ A A A c
  (fun x=>L (F x)) q a hOpenA (fun x (_:A x)=>iff_refl _) (fun x hx _=>hCA x hx) ha.
have hLast:=@norm_finite_jet_agreement_local R X Y NX NY hNX hNY Z ev NZ hZ B B B
  (fun x=>L (G x)) d q a hOpenB (fun x (_:B x)=>iff_refl _) (fun x hx _=>esym (hDB x hx)) hb.
exact:(norm_finite_jet_agreement_transitive (norm_finite_jet_agreement_transitive hFirst hEvaluationAgree) hLast).
Qed.
End CoefficientAgreement.
