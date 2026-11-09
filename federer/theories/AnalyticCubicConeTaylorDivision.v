(** Federer (1969), 3.4.5, p. 321: actual
    homogeneous Taylor coefficients of a function vanishing
    on the real cubic cone are divisible by its equation.
    This supports the example cited to Cartan (1957), pp. 97–99. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormAnalyticUP
  SymmetricForms SymmetricFormSum HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation
  PolynomialFunctions PolynomialRepresentations EuclideanCoordinateSplit
  CubicConePolynomialDivisibility CubicConeGeometry HomogeneousPolynomialFactorComponent AnalyticConeTaylorVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cubic_cone_taylor_factor]: each
    original actual homogeneous Taylor polynomial has an
    actual homogeneous quotient by the cubic equation;
    orders below three vanish. This supports the
    counterexample in 3.4.5, p. 321. No formal
    divisibility or analytic quotient is assumed. *)
Theorem analytic_cubic_cone_taylor_factor (R:realType) (NX:R_n R 3->R)
    (hNX:is_real_norm NX) (A:set (R_n R 3)) (f:R_n R 3->R):
  @norm_analytic R (R_n R 3) R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A f ->
  A 0 ->
  (forall x,A x ->cubic_cone_polynomial_value x=0 ->f x=0) ->
  forall m (z:@ContinuousMultilinear.space R m (R_n R 3) R^o NX (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R)),
  has_norm_higher_differential NX
    (fun i=>@ContinuousMultilinear.evaluation R i (R_n R 3) R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
    (fun i=>@ContinuousMultilinear.norm R i (R_n R 3) R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
    A f m 0 z ->
  exists (phi:S_m (R_n R 3) R^o m) (psi:S_m (R_n R 3) R^o (m-3)%N),
    (forall t,phi t=@ContinuousMultilinear.evaluation R m (R_n R 3) R^o NX (fun t=>`|t|)
      hNX (@scalar_absolute_value_norm R) [ffun i=>tnth t i] z) /\
    forall v,sform_polynomial_value phi v=if (m<3)%N then 0 else
      sform_polynomial_value psi v*cubic_cone_polynomial_value v.
Proof.
move=>hf hA hZero m z hz.
pose C:=fun v:R_n R 3=>cubic_cone_polynomial_value v=0.
have hScale v (hv:C v) (t:R) (_:0<t):C (t*:v).
  by rewrite /C cubic_cone_homogeneous hv mulr0.
have [phi [hActual hVanish]]:=@analytic_cone_taylor_polynomial_vanishing R (R_n R 3)
  NX hNX A C f hf hA hScale hZero m z hz.
pose P:=polynomial_from_forms (sform_include phi).
have hPValue v:P v=sform_polynomial_value phi v.
  by rewrite /P polynomial_from_formsE symmetric_polynomial_value_include.
have hParam s t:P (euclidean_join
    ((s*t*(1+t^+2))*:(@FiniteCoordinates.coordinate_basis R 2 ord0)+
      s*:(@FiniteCoordinates.coordinate_basis R 2 ord_max),s*(1+t^+2)))=0.
  rewrite hPValue;apply:hVanish;exact:(@cubic_cone_rational_point R s t).
have [Q hQ]:=@rational_cubic_cone_polynomial_divisible R P hParam.
pose psi:=sform_component (m-3)%N (polynomial_to_forms Q).
exists phi,psi;split;first exact:hActual.
apply:(@homogeneous_polynomial_factor_component R (R_n R 3) m 3%N Q
  (sform_polynomial_value phi) (@cubic_cone_polynomial_value R)).
- move=>t x;exact:(sform_polynomial_scale_argument phi t x).
- exact:(@cubic_cone_homogeneous R).
- move=>x;by rewrite -(hPValue x) hQ.
Qed.
