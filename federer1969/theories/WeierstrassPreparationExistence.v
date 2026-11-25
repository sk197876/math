(** Federer (1969), 3.4.6(2), pp. 322–324:
    the original analytic preparation follows by actual
    division of xi^k, retaining the supplied functional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormAnalyticUP NormAnalyticDomain
  NormAnalyticLinear NormAnalyticComposition NormAnalyticArithmetic NormAnalyticArithmeticLocal
  AnalyticGermNeighbourhood AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws
  AnalyticGermRing WeierstrassRegularUP WeierstrassDivisionUP WeierstrassDivisionWithTransverse
  WeierstrassTransverseUP WeierstrassCoefficientUP WeierstrassCoefficientExistence
  WeierstrassFunctionalPower WeierstrassPolynomialHighCoefficients WeierstrassFiniteRemainderRepresentation
  WeierstrassPreparationCoefficientValues WeierstrassZerothCoefficient WeierstrassPreparationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_preparation_with_transverse_exists]:
    the original monic Weierstrass polynomial, nonzero
    multiplier at zero, and analytic transverse coefficients
    vanishing at zero all exist, 3.4.6(2),
    p. 322. Divide the actual xi^k by the
    original phi, and negate the actual finite remainder
    coefficients. No prepared factor or vanishing conclusion
    is supplied as a premise. *)
Theorem weierstrass_preparation_with_transverse_exists (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (Phi:@analytic_germ_ring R X NX hNX 0):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->is_weierstrass_regular_germ Phi k v ->
  exists Q W:@analytic_germ_ring R X NX hNX 0,
    exists Wi:'I_k->@analytic_germ_ring R K NK hNK 0,
    @is_weierstrass_preparation R X K NX NK hNX hNK xi projection k Phi Q W Wi.
Proof.
move=>hSplit hXi hRegular.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
have [power [hPowerValues hPower]]:=@weierstrass_functional_power_representative R X NX hNX xi k hXi.
pose Psi:@analytic_germ_ring R X NX hNX 0:=analytic_germ power.
have [Q [T [hDivision _]]]:=@weierstrass_division_with_transverse R X K NX NK hNX hNK v xi inclusion projection
  k Phi Psi hSplit hXi hRegular.
have [phi hPhi]:=@weierstrass_split_coefficients_exist R X K NX hNX Phi v inclusion.
have [psi hPsi]:=@weierstrass_split_coefficients_exist R X K NX hNX Psi v inclusion.
have [q hQ]:=@weierstrass_split_coefficients_exist R X K NX hNX Q v inclusion.
have [r hR]:=@weierstrass_split_coefficients_exist R X K NX hNX T v inclusion.
have hMonic:=@weierstrass_functional_power_coefficients R X K NX NK hNX v xi inclusion projection k
  power psi hSplit hPowerValues hPower hPsi.
have [hLow hQNonzero]:=@weierstrass_preparation_coefficient_values R X K NX hNX v inclusion k
  Phi Psi Q T phi psi q r hRegular hDivision hPhi hPsi hQ hR hMonic.
have hHigh:=@weierstrass_polynomial_high_coefficients R X K NX hNX k v inclusion T r
  (weierstrass_division_polynomial_remainder hDivision) hR.
have [remainder [hRepR [C [hC [hCZero hRValues]]]]]:=@weierstrass_finite_remainder_representation
  R X K NX NK hNX hNK v xi inclusion projection k T r hSplit hXi hR hHigh.
have hEach (i:'I_k):exists c:analytic_representative_type hNK (0:K),
    analytic_representative_value c=(fun z=>-C i (inclusion z)).
  have hI:=@norm_bounded_linear_analytic R K X NK NX hNK hNX setT
    (fun z _=>norm_full_domain_interior NK z) inclusion (weierstrass_transverse_inclusion_bounded hSplit).
  have hAt:=hI 0 Logic.I.
  have hOuter:@norm_analytic_at R X R^o NX N hNX hN setT (C i) (inclusion 0).
    rewrite linear0;exact:hC i.
  have hComposite:=@norm_analytic_at_composition R K X R^o NK NX N hNK hNX hN
    setT setT inclusion (C i) 0 hAt hOuter.
  have hWhole:=@norm_analytic_at_domain_enlargement R K R^o NK N hNK hN
    (fun z=>setT z /\setT (inclusion z)) setT (fun z=>C i (inclusion z)) 0
    (fun z _=>Logic.I) hComposite.
  exact:(@analytic_representative_from_domain R K NK hNK 0 setT (fun z=>-C i (inclusion z))
    (@norm_analytic_at_negate R K R^o NK N hNK hN setT (fun z=>C i (inclusion z)) 0 hWhole)).
have [coefficients hCoefficients]:=choice hEach.
pose Wi (i:'I_k):@analytic_germ_ring R K NK hNK 0:=analytic_germ (coefficients i).
pose W:@analytic_germ_ring R X NX hNX 0:=Psi-T.
pose w:=@analytic_add_representatives R X NX hNX 0 power
  (@analytic_negate_representative R X NX hNX 0 remainder).
have hRepW:analytic_germ w=W.
  rewrite /W /Psi -hRepR.
  change (analytic_germ w=@AnalyticGerms.add R X NX hNX 0 (analytic_germ power)
    (@AnalyticGerms.opp R X NX hNX 0 (analytic_germ remainder))).
  by rewrite (@analytic_germ_negate_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0))
    (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0)).
exists Q,W,Wi;constructor.
- rewrite /W (weierstrass_division_identity hDivision) addrK;reflexivity.
- have [quotient hRepQ]:=@analytic_germ_has_representative R X NX hNX 0 Q.
  exists quotient;split;first exact:hRepQ.
  rewrite -(@weierstrass_zeroth_coefficient_value R X K NX hNX Q v inclusion (q 0%N 0%N)
    quotient (hQ 0%N 0%N) hRepQ (0:K)).
  exact:hQNonzero 0.
- exists w;split;first exact:hRepW.
  exists coefficients;split;first by move=>i.
  split.
  + move=>i;rewrite (hCoefficients i) /= linear0 hCZero (hLow i (ltn_ord i) 0) oppr0.
    reflexivity.
  + have [U [haU [_ [_ hw]]]]:=@analytic_germ_open_representative R X R^o NX N hNX hN
      setT (analytic_representative_value w) 0 (analytic_representative_analytic w).
    exists U;split;first exact:haU.
    split;first exact:hw.
    move=>x hx.
    change (analytic_representative_value power x+ -analytic_representative_value remainder x=
      (xi x)^+k+\sum_(i<k) (xi x)^+i*analytic_representative_value (coefficients i) (projection x)).
    rewrite hPowerValues hRValues.
    congr ((xi x)^+k+_).
    rewrite -sumrN;apply:eq_bigr=>i _.
    by rewrite (hCoefficients i) /= mulrN.
Qed.
