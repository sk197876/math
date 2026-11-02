(** Federer (1969), 3.2.22, p. 259: a
    nonnegative Borel weight for the ordinary mu-Jacobian
    of a composite constrained to a compact target chart. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP LipschitzUP LipschitzBasic NormMetricScaleContinuity EuclideanLebesgueDimensions
  MeasureUP MeasureAlmostUP MeasureAlmostBasic RectifiableCompactChartsUP
  EuclideanLinearJacobian TopMiddleJacobianComposition EuclideanFactorizedDifferentialsAlmost
  EuclideanJacobianBorelRepresentatives BorelFiniteRealProduct BorelFunctionUP BorelFunctionBasic
  RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coarea_chart_jacobian_borel_weight_exists]:
    supporting the local Jacobian integrals in Federer
    3.2.22, p. 259. Form the product of the
    exact Borel J_mu phi and J_mu gamma composed
    with phi representatives. Actual differential factorization
    proves almost-everywhere agreement with J_mu F on A.
    No arbitrary Lebesgue representative is pulled back through
    phi, and no derivative field or integrability is assumed. *)
Theorem coarea_chart_jacobian_borel_weight_exists (R:realType) m mu n
    (lambda:R) (A:set (R_n R m)) (C:set (R_n R mu))
    (F:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (phi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R mu))
    (gamma:R_n R mu->R_n R n):
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_metric_lipschitz setT F ->is_metric_lipschitz setT phi ->
  is_uniform_compact_rectifiable_chart lambda C gamma ->
  (forall a,A a ->C (phi a) /\ F a=gamma (phi a)) ->
  exists J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R,
    is_borel_function J /\ (forall a,0<=J a) /\
    measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A [set a|
      exists H:Hom (R_n R m) (R_n R n),
        has_norm_differential (inner_norm (@euclidean_inner_productP R m))
          (inner_norm (@euclidean_inner_productP R n)) setT F a H /\
        J a=euclidean_linear_jacobian mu H].
Proof.
move=>hA hF hPhi hChart hAgreement.
have [Jp [hJp [hJp0 hJpActual]]]:=euclidean_target_jacobian_borel_representative_exists hPhi.
have hGammaLip:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hChart).
have [Jg [hJg [hJg0 hJgActual]]]:=euclidean_top_jacobian_borel_representative_exists hGammaLip.
have hPhiCont:continuous phi.
  have [M [hM hBound]]:=hPhi.
  apply:(metric_fixed_lipschitz_continuous (ltW hM))=>a b; exact:(hBound.2 a b Logic.I Logic.I).
pose J:=fun a=>Jg (phi a)*Jp a.
have hJB:is_borel_function (fun a=>(J a:real_line_metric R)).
  exact:(borel_finite_real_product
    (borel_function_composition (continuous_borel_function hPhiCont) hJg) hJp).
exists J; split; first exact hJB; split.
- move=>a; exact:(mulr_ge0 (hJg0 (phi a)) (hJp0 a)).
- have hFactor:=euclidean_factorized_differentials_almost hA hF hPhi hChart hAgreement.
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m) _
    ((measure_almost_everywhere_on_implication _ _ _).1 hFactor))=>a hFactorA ha.
  have [H [L [D [hH [hL [hD [hEq hBounds]]]]]]]:=hFactorA ha.
  exists H; split; first exact hH.
  rewrite /J (hJgActual (phi a) D hD) (hJpActual a L hL) hEq.
  symmetry; exact:(euclidean_top_middle_jacobian_compose L D).
Qed.
