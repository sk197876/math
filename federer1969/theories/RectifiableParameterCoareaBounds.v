(** Federer (1969), 3.2.22, p. 259:
    the actual ordinary coordinate Jacobian and the
    intrinsic Jacobian times the source-area factor obey
    the two printed local integral comparison bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormDifferentialUP NormDifferentialDirectional LipschitzUP EuclideanLebesgueDimensions
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP MeasureApproximateJacobian
  RectifiableCompactChartsUP RectifiableParameterJacobianBounds EuclideanFactorizedDifferentialsAlmost
  EuclideanLinearJacobian LinearJacobianSandwich CoareaTargetChartJacobianBounds
  PositiveFactorSandwich CoareaParameterProductBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_parameter_coarea_product_bounds]:
    lambda^(-2mu-m) a_ij <= integral J_mu phi_ij
    <=lambda^(2mu+m) a_ij in Federer 3.2.22,
    p. 259, before integration. The source and
    target actual differentials, their exact factorization
    and the chart norm bounds prove the pointwise
    inequalities almost everywhere on A. *)
Theorem rectifiable_parameter_coarea_product_bounds (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (K A:set (R_n R m)) (C:set (R_n R mu))
    (psi:R_n R m->R_n R n) (F:R_n R n->R_n R v)
    (phi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R mu))
    (gamma:R_n R mu->R_n R v) (J0:R_n R n->R) (Js Jp:R_n R m->R):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->
  is_uniform_compact_rectifiable_chart lambda C gamma ->A `<=` K ->psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R v)) setT (fun a=>F (psi a)) ->
  is_metric_lipschitz setT phi ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  (forall a,A a ->C (phi a) /\ F (psi a)=gamma (phi a)) ->
  (forall w,0<=J0 w) ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  (forall a D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT psi a D ->Js a=euclidean_linear_jacobian m D) ->
  (forall a L,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R mu)) setT phi a L ->Jp a=euclidean_linear_jacobian mu L) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A [set a|
    J0 (psi a)*Js a<=lambda^+(mu+mu+m)*Jp a /\
    Jp a<=lambda^+(mu+mu+m)*(J0 (psi a)*Js a)].
Proof.
move=>hLambda hChart hTarget hAK hKW hW hFinite hF hFPsi hPhi hA hAgreement
  hJNonnegative hJ0 hJs hJp.
pose hm:=euclidean_lebesgue_is_measure R m.
have hSource:=rectifiable_parameter_jacobian_bounds hLambda hChart hKW hW hFinite hF hJ0.
have hFactor:=euclidean_factorized_differentials_almost hA hFPsi hPhi hTarget hAgreement.
have hBoth:=measure_almost_everywhere_and hm
  ((measure_almost_everywhere_on_implication _ _ _).1 hSource)
  ((measure_almost_everywhere_on_implication _ _ _).1 hFactor).
have hPos:0<lambda:=lt_trans ltr01 hLambda.
have hPow:0<lambda^+mu:=exprn_gt0 mu hPos.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hm _ hBoth)=>a [hSourceA hFactorA] ha.
have hKa:=hAK a ha.
have [Ds [H [hDs [hH hSourceBounds]]]]:=hSourceA hKa.
have [H0 [L [Dt [hH0 [hL [hDt [hEq hTargetBounds]]]]]]]:=hFactorA ha.
have hHEq:H0=H:=@norm_differential_unique R (R_n R m) (R_n R v)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R v))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R v))
  setT (fun x=>F (psi x)) a H0 H hH0 hH.
have hTargetSandwich:=@coarea_target_chart_jacobian_bounds R m mu v L Dt lambda hPos
  (fun x=>(hTargetBounds x).1) (fun x=>(hTargetBounds x).2).
rewrite -hEq hHEq in hTargetSandwich.
have hCoordinate:=iterated_positive_factor_sandwich hPow hSourceBounds.1 hSourceBounds.2
  hTargetSandwich.1 hTargetSandwich.2.
rewrite -exprD -(hJp a L hL) in hCoordinate.
have [Ds0 [hDs0 hDsBounds]]:=rectifiable_chart_differential_bounds hChart hKa.
have hDEq:Ds0=Ds:=@norm_differential_unique R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  setT psi a Ds0 Ds hDs0 hDs.
rewrite hDEq in hDsBounds.
have hInv:0<=lambda^-1 by rewrite invr_ge0; exact:ltW hPos.
have hJsBounds:=euclidean_top_jacobian_sandwich hInv (ltW hPos)
  (fun x=>(hDsBounds x).1) (fun x=>(hDsBounds x).2).
rewrite exprVn -(hJs a Ds hDs) in hJsBounds.
have hResult:=coarea_parameter_product_bounds (exprn_gt0 (mu+mu) hPos)
  (exprn_gt0 m hPos) (hJNonnegative (psi a)) hCoordinate.1 hCoordinate.2 hJsBounds.1 hJsBounds.2.
by rewrite -exprD in hResult.
Qed.
