(** Federer (1969), 3.4.7, p. 325: xi is
    transcendental over the original transverse analytic germ
    ring. Actual finite representatives and local short-line
    coefficient uniqueness prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LocalGermUP LocalGermSealed
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws AnalyticGermRing AnalyticTransversePolynomialRepresentative
  TransversePolynomialLocalIndependence WeierstrassTransverseUP WeierstrassTransversePullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Independence.
Variable R:realType.
Variables X K:lmodType R.
Variable NX:X->R.
Variable NK:K->R.
Hypothesis hNX:is_real_norm NX.
Hypothesis hNK:is_real_norm NK.
Variable v:X.
Variable xi:Hom X R^o.
Variable inclusion:Hom K X.
Variable projection:Hom X K.
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
Local Notation E:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).

(** Source for [analytic_transverse_coefficients_independent]: an
    actual finite relation in powers of the original
    xi germ has every transverse coefficient zero,
    the transcendence assertion of 3.4.7, p. 325. *)
Theorem analytic_transverse_coefficients_independent k (alpha:nat->A):
  (forall x,analytic_representative_value fXi x = xi x) ->
  (\sum_(i<k) E (alpha i)*Gamma^+i) = 0 ->
  forall i,(i<k)%N ->alpha i = 0.
Proof.
move=>hXi hZero.
pose TX:=Topological.clone (real_norm_metric_space hNX) _.
pose TK:=Topological.clone (real_norm_metric_space hNK) _.
pose PX:=@analytic_representative_type R X NX hNX 0.
pose PK:=@analytic_representative_type R K NK hNK (projection 0).
have hGX:=@LocalGerms.laws TX R PX (@analytic_representative_value R X NX hNX 0) 0.
have hGK:=@LocalGerms.laws TK R PK (@analytic_representative_value R K NK hNK (projection 0)) (projection 0).
have hRepresentatives i:=@analytic_germ_has_representative R K NK hNK (projection 0) (alpha i).
pose c i:=projT1 (cid (hRepresentatives i)).
have hC i:analytic_germ (c i) = alpha i:=projT2 (cid (hRepresentatives i)).
have [f [hValues hGerm]]:=@analytic_transverse_polynomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi k c hXi.
have hSum:(\sum_(i<k) E (analytic_germ (c i))*Gamma^+i) = \sum_(i<k) E (alpha i)*Gamma^+i.
  apply:eq_bigr=>i _;by rewrite hC.
have hGermZero:(analytic_germ f:G) = 0 by rewrite hGerm hSum.
pose zeroX:=@analytic_constant_representative R X NX hNX 0 0.
have hGermEqual:analytic_germ f = analytic_germ zeroX:=hGermZero.
have [U [hU [hUOrigin hAgreement]]]:=(local_germ_equality hGX f zeroX).1 hGermEqual.
have hPolynomial x:U x ->\sum_(i<k) (xi x)^+i*analytic_representative_value (c i) (projection x) = 0.
  move=>hx;rewrite -hValues;exact:hAgreement x hx.
have [B [hBOpen [hBOrigin hCoefficients]]]:=@transverse_polynomial_local_independence R X K
  NX NK hNX hNK v xi inclusion projection hSplit k
  (fun i=>analytic_representative_value (c i)) U hU hUOrigin hPolynomial.
move=>i hi;rewrite -(hC i).
change (analytic_germ (c i) = analytic_germ (@analytic_constant_representative R K NK hNK (projection 0) 0)).
apply/(local_germ_equality hGK _ _).
exists B;split;first exact:hBOpen.
split;first by rewrite (linear0 projection).
move=>z hz;change (analytic_representative_value (c i) z = 0).
exact:hCoefficients z hz i hi.
Qed.
End Independence.
