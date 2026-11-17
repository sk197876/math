(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: xi is
    transcendental over the original transverse analytic germ
    ring. Actual finite representatives and local short-line
    coefficient uniqueness prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormMetric LocalGermUP LocalGermSealed
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermRing HolomorphicTransversePolynomialRepresentative
  ComplexTransversePolynomialLocalIndependence ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Independence.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable NK:K->R.
Hypothesis hNX:is_complex_norm NX.
Hypothesis hNK:is_complex_norm NK.
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variable inclusion:Hom K X.
Variable projection:Hom X K.
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
Local Notation E:=(@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(holomorphic_germ fXi:G).

(** Source for [holomorphic_transverse_coefficients_independent]: an
    actual finite relation in powers of the original
    xi germ has every transverse coefficient zero,
    the transcendence assertion of 3.4.7, p. 325. *)
Theorem holomorphic_transverse_coefficients_independent k (alpha:nat->A):
  (forall x,holomorphic_representative_value fXi x = xi x) ->
  (\sum_(i<k) E (alpha i)*Gamma^+i) = 0 ->
  forall i,(i<k)%N ->alpha i = 0.
Proof.
move=>hXi hZero.
pose TX:=Topological.clone (real_norm_metric_space (complex_norm_real hNX)) _.
pose TK:=Topological.clone (real_norm_metric_space (complex_norm_real hNK)) _.
pose PX:=@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
pose PK:=@holomorphic_representative_type R K NK (complex_norm_real hNK) (projection 0).
have hGX:=@LocalGerms.laws TX (ComplexScalars.C R) PX (@holomorphic_representative_value R X NX (complex_norm_real hNX) 0) 0.
have hGK:=@LocalGerms.laws TK (ComplexScalars.C R) PK (@holomorphic_representative_value R K NK (complex_norm_real hNK) (projection 0)) (projection 0).
have hRepresentatives i:=@holomorphic_germ_has_representative R K NK (complex_norm_real hNK) (projection 0) (alpha i).
pose c i:=projT1 (cid (hRepresentatives i)).
have hC i:holomorphic_germ (c i) = alpha i:=projT2 (cid (hRepresentatives i)).
have [f [hValues hGerm]]:=@holomorphic_transverse_polynomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi k c hXi.
have hSum:(\sum_(i<k) E (holomorphic_germ (c i))*Gamma^+i) = \sum_(i<k) E (alpha i)*Gamma^+i.
  apply:eq_bigr=>i _;by rewrite hC.
have hGermZero:(holomorphic_germ f:G) = 0 by rewrite hGerm hSum.
pose zeroX:=@holomorphic_constant_representative R X NX (complex_norm_real hNX) 0 0.
have hGermEqual:holomorphic_germ f = holomorphic_germ zeroX:=hGermZero.
have [U [hU [hUOrigin hAgreement]]]:=(local_germ_equality hGX f zeroX).1 hGermEqual.
have hPolynomial x:U x ->\sum_(i<k) (xi x)^+i*holomorphic_representative_value (c i) (projection x) = 0.
  move=>hx;rewrite -hValues;exact:hAgreement x hx.
have [B [hBOpen [hBOrigin hCoefficients]]]:=@complex_transverse_polynomial_local_independence R X K
  NX NK hNX hNK v xi inclusion projection hSplit k
  (fun i=>holomorphic_representative_value (c i)) U hU hUOrigin hPolynomial.
move=>i hi;rewrite -(hC i).
change (holomorphic_germ (c i) = holomorphic_germ (@holomorphic_constant_representative R K NK (complex_norm_real hNK) (projection 0) 0)).
apply/(local_germ_equality hGK _ _).
exists B;split;first exact:hBOpen.
split;first by rewrite (linear0 projection).
move=>z hz;change (holomorphic_representative_value (c i) z = 0).
exact:hCoefficients z hz i hi.
Qed.
End Independence.
