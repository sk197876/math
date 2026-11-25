(** Federer (1969), 4.1.2, p. 347: bounded
    linear maps commute with the actual vector integral.
    This follows from the defining continuous-dual evaluations
    in 2.4.12, p. 87. The image retains the
    original L1 domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormDifferentialUP NormBoundedLinearTopology
  ScalarNormExtendedEmbedding ContinuousRealFunctional PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureLpMembershipUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_vector_integral_linear_image]: the
    original continuous-dual characterization proves the linear
    interchange needed for the derivative-space identity in
    Federer 4.1.2, p. 347. Actual L1
    membership of the image is stated explicitly. *)
Theorem total_vector_integral_linear_image (R:realType) (X:choiceType)
    (Y Z:lmodType R) (NY:Y->R) (NZ:Z->R)
    (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (mu:set X->\bar R) (L:Hom Y Z) (f:X->Y) y:
  norm_bounded_linear NY NZ L ->
  is_measure_lp_function mu 1
    (partial_function_total (fun x=>(L (f x):real_norm_metric_space hNZ))) ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) y ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(L (f x):real_norm_metric_space hNZ))) (L y).
Proof.
move=>hL hLone hI; split; first exact hLone.
move=>a ha.
pose b:{linear Y->R^o}:=hom_as_linear (hom_comp (hom_of_linear a) L).
have hContinuous:=@norm_bounded_linear_continuous R Y Z NY NZ hNY hNZ L hL.
have hb:is_continuous_real_functional hNY b.
  move=>z.
  change ((fun w:real_norm_metric_space hNY=>(a (L w):real_line_metric R)) @
    (z:real_norm_metric_space hNY) --> (a (L z):real_line_metric R)).
  exact:continuous_comp (hContinuous z) (ha (L z)).
have hScalar:=hI.2 b hb.
have hValue:b y=a (L y) by rewrite /b hom_as_linearE hom_compE.
rewrite hValue in hScalar.
apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hScalar)=>x r.
split.
- move=>[v [hv he]]; change (f x=v) in hv.
  exists (L v); split; first by change (L (f x)=L v); rewrite hv.
  exact he.
- move=>[v [hv he]]; change (L (f x)=v) in hv.
  exists (f x); split; first reflexivity.
  change ((a (L (f x)))%:E=r); by rewrite hv.
Qed.
