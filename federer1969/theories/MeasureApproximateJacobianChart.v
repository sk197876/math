(** Federer (1969), 3.2.20, p. 257: the actual
    approximate-Jacobian product in an injective differential chart.
    Use only the approximate differential's exact partial graph and
    the intrinsic exterior norm's independent laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP HilbertFormCompactness NormDifferentialUP PartialFunctionUP
  PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPrecomposition
  MeasureRestriction HausdorffMeasure MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureApproximateJacobianUP PartialLinearChartGraph PartialExteriorTopChart
  EuclideanLinearJacobian RectifiableDifferentialChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_differential_specification_domain]:
    the exact tangent-cone domain in Federer 3.2.16, p. 253,
    used in the Jacobian product of 3.2.20, p. 257.
    This consequence holds for every partial map satisfying the abstract
    differential specification, not just for a selected representative. *)
Lemma measure_approximate_differential_specification_domain (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (phi : set X -> \bar R) m
    (f : partial_function X Y) a (d : partial_function X Y) :
  is_measure_approximate_differential NY hNX phi m f a d ->
  partial_function_domain d=measure_approximate_tangent_cone hNX phi m a.
Proof.
move=> hd; apply/seteqP; split.
- by move=> v [y hvy]; exact: ((hd.2 v y).1 hvy).1.
- move=> v hv; have [D hD] := hd.1; exists (D v).
  apply: (hd.2 v (D v)).2; split; first exact hv.
  exists D; by split.
Qed.

(** Source for [rectifiable_differential_chart_jacobian]: the first
    display in the proof of Federer 3.2.20, p. 257:
    ap J_m f(psi(a))*J_m psi(a)=J_m(F composed with psi)(a).
    The chart-point laws of 3.2.19 supply both actual source
    differentials, the exact tangent plane and partial chain rule.
    This lemma discharges the intrinsic norm calculation without assuming
    a Jacobian composition identity or arbitrary off-tangent derivatives. *)
Theorem rectifiable_differential_chart_jacobian (R : realType) m n k
    (W : set (R_n R n)) (K : set (R_n R m))
    (psi : R_n R m -> R_n R n) (F : R_n R n -> R_n R k) w :
  is_rectifiable_differential_chart_point W K psi F w ->
  exists a (D : Hom (R_n R m) (R_n R n)) (H : Hom (R_n R m) (R_n R k)) (j : R),
    K a /\ psi a=w /\ injective D /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H /\
    has_measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m m
      (partial_function_source_restrict W (partial_function_total F)) w j /\
    j*euclidean_linear_jacobian m D=euclidean_linear_jacobian m H.
Proof.
move=> [a [D [H [d [ha [hVal [hInj [hD [hH [hCone [hApx hComp]]]]]]]]]]].
have hDom := measure_approximate_differential_specification_domain hApx.
rewrite hCone in hDom.
have hGraph := partial_linear_chart_graph hDom hComp.
have hNorm := partial_exterior_norm_injective_chart hInj hGraph.
exists a,D,H,(euclidean_linear_jacobian m H/euclidean_linear_jacobian m D).
split; first exact ha.
split; first exact hVal.
split; first exact hInj.
split; first exact hD.
split; first exact hH.
split; first by exists d; split.
have hPositive := (euclidean_linear_jacobian_top_positive D).2 hInj.
have hNonzero : euclidean_linear_jacobian m D!=0 by rewrite (gt_eqF hPositive).
by rewrite divfK //.
Qed.
