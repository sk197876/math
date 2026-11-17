(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: each positive
    derivative of pullback is bounded by a constant times
    finitely many original outer derivatives. The actual constant
    comes from 3.1.11's finite composition sum, p. 222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicAtUP HolomorphicAtAnalytic HolomorphicGermAnalytic Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityOperations
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherSymmetricFormUP NormHigherSymmetricFormFamilies
  NormHigherCompositionFormula NormSmoothFields SymmetricForms SymmetricOperatorNorm
  SymmetricMultiIndices SymmetricDividedMonomials CompositionMultiIndices CompositionFormCoefficient
  CompositionFiniteOuterBound NormAnalyticUP NormAnalyticBoundNonnegative
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermGrowthUP
  HolomorphicGermJetsSealed HolomorphicGermRealCoefficientForms HolomorphicGermFormActual
  HolomorphicPullbackRepresentative HolomorphicPullbackUP HolomorphicPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_pullback_positive_jet_bound]:
    continuity of every positive derivative coordinate of the
    original homomorphism in 3.4.5, p. 319. The
    source map and centre are fixed; no bound on its
    derivatives is supplied as a new theorem hypothesis. *)
Theorem holomorphic_germ_pullback_positive_jet_bound (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (u:X->Y) a
    (hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a) m:
  (1<=m)%N ->exists K:R,0<=K /\forall (alpha:holomorphic_germ_space hNY (u a)) (B:R),
    0<=B ->(forall i,(i<=m)%N ->@holomorphic_germ_jet_norm R Y NY hNY (u a) i alpha<=B) ->
    @holomorphic_germ_jet_norm R X NX hNX a m
      (@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu alpha)<=K*B.
Proof.
move=>hm.
pose NS:=@complex_modulus R.
pose hNS:=@complex_modulus_real_norm R.
pose Z i:=@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY.
pose ez i:=@ContinuousMultilinear.evaluation R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY.
pose NZ i:=@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY.
pose W i:=@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY NS hNY hNS.
pose ew i:=@ContinuousMultilinear.evaluation R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY NS hNY hNS.
pose NW i:=@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY NS hNY hNS.
pose hW i:=@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY NS hNY hNS.
pose T i:=@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
pose et i:=@ContinuousMultilinear.evaluation R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
pose NT i:=@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
pose hT i:=@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
have [U [c [hUa [hUA [hClassU hBoundU]]]]]:=holomorphic_at_analytic hu.
have hc:=norm_analytic_operator_witness_nonnegative hUa hClassU hBoundU.
have [D hD]:=@norm_smooth_fields_exist R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY U u hClassU.
have [phi hPhi]:=@norm_higher_differential_point_forms R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY
  Z ez NZ hZ U u m a (fun i=>D i a) (fun i _=>(hD i).1 a hUa).
pose C (i:'I_m):=c^+(val i).+1*((val i).+1`!)%:R.
have hC i:0<=C i:=mulr_ge0 (exprn_ge0 _ hc) (ler0n _ _).
have hPhiBound i:(@symmetric_operator_norm R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX hNX.1 NY (val i).+1 (phi (val i).+1)<=(C i)%:E)%E.
  rewrite (hPhi _ (valP i)).2 lee_fin.
  have hPositive:(1<=(val i).+1)%N by [].
  exact:(hBoundU _ hPositive a hUa (D _ a) ((hD _).1 a hUa)).
pose L:R:=\sum_(alpha:composition_indices m m)
  ((m`!)%:R/(symmetric_multi_factorial (composition_indices_unbound alpha))%:R)*
    symmetric_scalar_monomial (fun i:'I_m=>C i/((val i).+1`!)%:R)
      (composition_indices_unbound alpha).
pose K:R:=`|L|.
exists K;split;first exact:normr_ge0.
move=>alpha B hB hAlpha.
have [f hf]:=@holomorphic_germ_has_representative R Y NY hNY (u a) alpha.
have [V [d [hVa [hVT [hClassV hBoundV]]]]]:=holomorphic_representative_analytic f.
pose H:=fun x=>U x /\ V (u x).
have hHa:H a by split.
have hClassH i:=@norm_class_composition R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NY NS hNX hNY hNS
  U V u (holomorphic_representative_value f) i (hClassU i) (hClassV i).
have hOpenV x (hx:V x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY V x:=((hClassV 0%N).1 x hx).1.
have hOpenH x (hx:H x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX H x:=((hClassH 0%N).1 x hx).1.
have [psi [hPsi [hPsiFinite hPsiNorm]]]:=@holomorphic_germ_coefficient_forms_exists R Y NY hNY (u a) alpha.
have hActualPsi i:@is_norm_higher_differential_form R (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY W ew NW V (holomorphic_representative_value f) i (u a) (psi i).
  exact:(@holomorphic_germ_coefficient_actual_on_neighbourhood R Y NY hNY (u a) i alpha f V (psi i)
    hf hVa hOpenV (hPsi i)).
pose beta:=@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu alpha.
have [eta [hEta [hEtaFinite hEtaNorm]]]:=@holomorphic_germ_coefficient_forms_exists R X NX hNX a beta.
pose g:=@holomorphic_pullback_representative R X Y NX NY hNX hNY A u a hu f.
have hg:holomorphic_germ g=beta by rewrite /beta -hf (@HolomorphicPullback.laws R X Y NX NY hNX hNY A u a hu).
have hActualEta:=@holomorphic_germ_coefficient_actual_on_neighbourhood R X NX hNX a m beta g H (eta m)
  hg hHa hOpenH (hEta m).
have hmm:(1<=m<=m)%N by rewrite hm leqnn.
have hEquation:=@norm_higher_composition_formula R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NY NS hNX hNY hNS
  Z W T ez NZ ew NW et NT hZ hW hT U V u (holomorphic_representative_value f) m a phi psi
  hm hUa hVa (hClassU m) (hClassV m) (fun i hi=>(hPhi i hi).1)
  (fun i _=>hActualPsi i) m hmm (eta m) hActualEta.
have hPsiBound j (hj:(1<=j<=m)%N):(@symmetric_operator_norm R (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY hNY.1 NS j (psi j)<=B%:E)%E.
  rewrite hPsiNorm lee_fin;exact:hAlpha j (andP hj).2.
have hEstimate:=@composition_form_finite_outer_bound R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NY NS hNX hNY hNS
  m phi psi C B hm hC hPhiBound hB hPsiBound.
rewrite -hEquation hEtaNorm lee_fin in hEstimate.
apply:le_trans hEstimate _.
rewrite [K*B]mulrC.
change (is_true (B*L<=B*`|L|)).
have hMultiply:=ler_wpM2r hB (ler_norm L).
by rewrite ![_*B]mulrC in hMultiply.
Qed.
