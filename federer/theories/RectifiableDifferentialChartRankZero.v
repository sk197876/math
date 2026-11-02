(** Federer (1969), 3.2.22, pp. 258–259:
    deficient rank of the source-chart differential forces
    the actual intrinsic approximate Jacobian to be zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureRestriction HausdorffMeasure MeasureApproximateDifferentialUP MeasureApproximateJacobianUP
  MeasureApproximateJacobianChart PartialLinearChartGraph LinearRankAtLeast ExteriorRankZero
  RectifiableCompactChartsUP RectifiableCompactChartLaws RectifiableDifferentialChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_differential_chart_rank_zero]:
    the implication from deficient chart rank to ap J_mu f=0
    above Q in Federer 3.2.22, pp. 258–259.
    Uniqueness identifies an actual supplied composite
    differential with that in the exact approximate chain
    rule of 3.2.19. Its deficient output image annihilates
    every actual exterior word of the partial differential. *)
Theorem rectifiable_differential_chart_rank_zero (R:realType) m n k q
    (lambda:R) (W:set (R_n R n)) (K:set (R_n R m))
    (psi:R_n R m->R_n R n) (F:R_n R n->R_n R k) a
    (H0:Hom (R_n R m) (R_n R k)):
  is_uniform_compact_rectifiable_chart lambda K psi ->K a ->
  is_rectifiable_differential_chart_point W K psi F (psi a) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H0 ->
  ~linear_rank_at_least H0 q ->
  has_measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W) m q
    (partial_function_source_restrict W (partial_function_total F)) (psi a) 0.
Proof.
move=>hChart ha [b [D [H [d [hb [hVal [hInj [hD [hH [hCone [hApx hComp]]]]]]]]]]] hH0 hRank.
have hba:b=a:=@uniform_compact_chart_injective R m n lambda K psi hChart b a hb ha hVal.
rewrite hba in hH.
have hEq:H=H0:=@norm_differential_unique R (R_n R m) (R_n R k)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R k))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H H0 hH hH0.
have hDom:=measure_approximate_differential_specification_domain hApx.
rewrite hCone in hDom; have hGraph:=partial_linear_chart_graph hDom hComp.
exists d; split; first exact hApx.
apply:(@partial_exterior_low_rank_norm_zero R m n k q H0 d hRank)=>v w hvw.
have [x [hDx hHx]]:=(hGraph v w).1 hvw.
exists x; by rewrite -hEq.
Qed.
