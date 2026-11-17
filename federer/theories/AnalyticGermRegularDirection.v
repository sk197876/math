(** Federer (1969), 3.4.7, pp. 324–325:
    choose a direction at which the first nonzero
    derivative has nonzero diagonal value. Polarization proves
    this existence assertion before the exceptional-set measure
    calculation; no direction is a theorem hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricFormWords SymmetricFormExtension
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermCoefficientForms
  AnalyticGermFirstNonzeroJet WeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_regular_direction_exists]:
    the direction chosen for the ideal argument in
    3.4.7, p. 325. Any nonzero germ with
    zero zeroth derivative has actual positive finite
    directional order along some vector. The proof
    works without finite dimension or completeness. *)
Theorem analytic_germ_regular_direction_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (alpha:analytic_germ_space hNX (0:X)):
  alpha<>@analytic_germ_zero R X NX hNX 0 ->
  @AnalyticGermJets.value R X NX hNX 0 0%N alpha = 0 ->
  exists k,exists v:X,is_weierstrass_regular_germ alpha k v.
Proof.
move=>hAlpha hZeroth.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|)
  hNX (@scalar_absolute_value_norm R).
pose jet:=@AnalyticGermJets.value R X NX hNX 0.
have [k [hk hLower]]:=analytic_germ_first_nonzero_jet hAlpha.
have hPositive:(0<k)%N.
  case:k hk hLower=>[|k] hk hLower;last by [].
  exfalso;apply:hk;exact:hZeroth.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
have hForm:F k<>0.
  move=>hZero;apply:hk.
  apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R k X R^o NX
    (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)))=>u.
  have hTuple:[ffun j=>tnth [tuple u i|i<k] j] = u.
    by apply/ffunP=>j;rewrite ffunE tnth_mktuple.
  have hh:=hF k [tuple u i|i<k].
  rewrite hZero sform_zeroE hTuple in hh.
  by rewrite linear0;exact:esym hh.
have hNonzero:exists v:X,sform_polynomial_value (F k) v<>0.
  apply:contrapT=>hNo;apply:hForm.
  apply:(@sform_polynomial_zero_iff R X R^o k (@pchar_num R) (F k)).1=>v.
  apply:contrapT=>h;apply:hNo;by exists v.
have [v hv]:=hNonzero.
exists k,v;split;first exact:hPositive.
split.
- move=>i hi;by rewrite (hLower i hi) linear0.
- move=>hZero;apply:hv.
  rewrite sform_polynomial_diagonal_value.
  have hh:=hF k [tuple v|_<k].
  have hTuple:[ffun j:'I_k=>tnth [tuple v|_<k] j] = [ffun _:'I_k=>v].
    by apply/ffunP=>j;rewrite !ffunE tnth_mktuple.
  by rewrite hh hTuple hZero scaler0.
Qed.
