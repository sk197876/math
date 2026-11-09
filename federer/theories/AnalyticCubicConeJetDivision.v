(** Federer (1969), 3.4.5, p. 321: every actual
    finite Taylor jet of a function vanishing on the
    real cubic cone is divisible by its equation.
    This supports the example cited to Cartan (1957), pp. 97–99. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateSplit
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormAnalyticUP
  NormAnalyticLocal NormSmoothFields SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  PolynomialFunctions NormTaylorRemainderBound NormJetUP NormJetSealed
  CubicConePolynomialDivisibility CubicConeGeometry AnalyticCubicConeTaylorDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section JetDivision.
Variable R:realType.
Local Notation X:=(R_n R 3).
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X R^o NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X R^o NX N hNX hN).

(** Source for [analytic_cubic_cone_jet_divisible]: an
    actual Taylor jet satisfying the original jet laws
    is a polynomial multiple of the actual cubic,
    supporting the counterexample in 3.4.5, p. 321. *)
Theorem analytic_cubic_cone_jet_divisible (A:set X) (f:X->R) k
    (P:PolynomialFunction X R^o):
  @norm_analytic R X R^o NX N hNX hN A f ->A 0 ->
  (forall x,A x ->cubic_cone_polynomial_value x=0 ->f x=0) ->
  is_norm_jet_polynomial NX ev NZ A f k 0 P ->
  exists Q:PolynomialFunction X R^o,forall v,P v=Q v*cubic_cone_polynomial_value v.
Proof.
move=>hf hA hZero hP.
have hCone v (hv:cubic_cone_polynomial_value v=0):P v=0.
  have [D [hD hValue]]:=norm_jet_polynomial_expansion hP.
  rewrite hValue /norm_taylor_value subr0.
  apply:big1=>m _.
  have hm:(m<=k)%N by have:=ltn_ord m;rewrite ltnS.
  have [phi [psi [hActual hFactor]]]:=@analytic_cubic_cone_taylor_factor R NX hNX A f
    hf hA hZero m (D m) (hD m hm).
  have hPhiZero:=hFactor v.
  rewrite hv mulr0 if_same in hPhiZero.
  rewrite sform_polynomial_diagonal_value hActual in hPhiZero.
  have hArguments:[ffun i:'I_m=>tnth [tuple v|_<m] i]=[ffun _:'I_m=>v].
    by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
  by rewrite hArguments in hPhiZero.
apply:(@rational_cubic_cone_polynomial_divisible R P)=>s t.
exact:(hCone _ (@cubic_cone_rational_point R s t)).
Qed.

(** Source for [analytic_cubic_cone_finite_jet_division]:
    for every finite order, an actual Taylor jet
    and an actual polynomial quotient exist. The
    opaque original jet supplies the coefficients and
    finite real polynomial division proves the quotient,
    supporting 3.4.5, p. 321. *)
Theorem analytic_cubic_cone_finite_jet_division (A:set X) (f:X->R) k:
  @norm_analytic R X R^o NX N hNX hN A f ->A 0 ->
  (forall x,A x ->cubic_cone_polynomial_value x=0 ->f x=0) ->
  exists P Q:PolynomialFunction X R^o,
    is_norm_jet_polynomial NX ev NZ A f k 0 P /\
    forall v,P v=Q v*cubic_cone_polynomial_value v.
Proof.
move=>hf hA hZero.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX N hNX hN A f
  (norm_analytic_class_all_orders hf).
pose hz:=(hD k).1 0 hA.
pose P:=@NormJet.value R X R^o NX N hNX hN Z ev NZ hZ A f k 0 (D k 0) hz.
have hP:=@NormJet.laws R X R^o NX N hNX hN Z ev NZ hZ A f k 0 (D k 0) hz.
have [Q hQ]:=analytic_cubic_cone_jet_divisible hf hA hZero hP.
by exists P,Q.
Qed.
End JetDivision.
