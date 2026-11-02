(** Federer (1969), 3.2.22, p. 259: lower-degree
    approximate Jacobian bounds at an actual rectifiable
    differential chart point. All analytic chart-point laws
    are supplied separately by 3.2.19. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureRestriction HausdorffMeasure MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureApproximateJacobianUP MeasureApproximateJacobianChart PartialLinearChartGraph
  PartialExteriorChartCoordinates PartialExteriorChartSandwich EuclideanLinearJacobian
  RectifiableCompactChartsUP RectifiableDifferentialChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_differential_chart_jacobian_sandwich]:
    lambda^(-mu) ap J_mu f(psi(a)) <= J_mu(F composed
    with psi)(a) <= lambda^mu ap J_mu f(psi(a)) in
    Federer 3.2.22, p. 259. Extract the actual
    partial graph from the exact approximate chain rule of
    3.2.19 and apply the all-degree linear comparison.
    No additional derivative, domain or exterior-norm identity
    is assumed. Degree zero is included. *)
Theorem rectifiable_differential_chart_jacobian_sandwich (R:realType) m n k q
    (lambda:R) (W:set (R_n R n)) (K:set (R_n R m))
    (psi:R_n R m->R_n R n) (F:R_n R n->R_n R k) w:
  1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->
  is_rectifiable_differential_chart_point W K psi F w ->
  exists a (D:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R k)) (j:R),
    K a /\ psi a=w /\ injective D /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H /\
    has_measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m q
      (partial_function_source_restrict W (partial_function_total F)) w j /\
    (lambda^+q)^-1*j<=euclidean_linear_jacobian q H /\
      euclidean_linear_jacobian q H<=lambda^+q*j.
Proof.
move=>hLambda hChart [a [D [H [d [ha [hVal [hInj [hD [hH [hCone [hApx hComp]]]]]]]]]]].
have hDom:=measure_approximate_differential_specification_domain hApx.
rewrite hCone in hDom; have hGraph:=partial_linear_chart_graph hDom hComp.
have [L [K0 [Ki [hNorm _]]]]:=@partial_exterior_chart_coordinates_exists R m n k q D H d hInj hGraph.
have [D0 [hD0 hBounds]]:=rectifiable_chart_differential_bounds hChart ha.
have hEq:D0=D:=@norm_differential_unique R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) setT psi a D0 D hD0 hD.
rewrite hEq in hBounds.
have hPositive:0<lambda:=lt_trans ltr01 hLambda.
have hSandwich:=@partial_exterior_chart_jacobian_sandwich R m n k q D H d lambda
  (euclidean_linear_jacobian q L) hInj hPositive hGraph
  (fun x=>(hBounds x).1) (fun x=>(hBounds x).2) hNorm.
exists a,D,H,(euclidean_linear_jacobian q L).
split; first exact ha; split; first exact hVal; split; first exact hInj.
split; first exact hD; split; first exact hH; split; last exact hSandwich.
exists d; by split.
Qed.
