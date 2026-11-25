(** Federer (1969), 4.1.4, p. 349: for each original
    test supported in A, the smooth density integral equals
    the constant on C_e applied to its actual vector integral
    at every sufficiently small scale. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric ContinuousDualUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  PartialFunctionBasic MeasureVectorIntegralUP EuclideanLebesgueDimensions DistributionIntegralFieldUP
  DistributionConstantDensityAction InnerParallelFamilyUP InnerComponentFamilyUP InnerComponentExhaustion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section InnerConstantIntegralEvaluation.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y N hN (fun _=>True) DT value).
Variable T:Hom DT R^o.
Variable Q:R->Hom DT DT.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable g:R->X->YD.
Hypothesis hAction:forall e:R,0<e ->
  is_distribution_integral_action (@euclidean_lebesgue_measure R n) ed (g e) value (hom_comp T (Q e)).
Variable A:set X.
Hypothesis hOpen:@open NT A.
Hypothesis hConnected:@connected NT A.
Variable O:R->set X.
Hypothesis hO:is_inner_parallel_family N A O.
Variable a:X.
Hypothesis ha:A a.
Variable C:R->set X.
Hypothesis hC:@is_inner_component_family R NT O a C.
Hypothesis hConst:forall e:R,0<e ->forall u v,C e u ->C e v ->g e v=g e u.

(** Source for [inner_constant_integral_eventual_evaluation]:
    compact capture makes the first original integral formula
    in Federer 4.1.4, p. 349, valid with the actual constant
    g_e(a) at all sufficiently small positive scales. *)
Theorem inner_constant_integral_eventual_evaluation (f:DT) (v:Y):
  support f `<=` A ->is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun x=>(value f x:real_norm_metric_space hNY))) v ->
  exists d:R,0<d /\ forall e:R,0<e ->e<d ->T (Q e f)=ed (g e a) v.
Proof.
move=>hSupp hVector.
have hCompact:@compact NT (support f):=smooth_test_support_compact hE f.
pose L:=@Build_smooth_compact_set R X N hN A (support f) hSupp hCompact.
pose L0:=@smooth_compact_union R X N hN A L (@smooth_compact_singleton R X N hN A a ha).
have[d [hd hCapture]]:=@inner_component_eventually_contains_compact R X N hN A hOpen hConnected
  O hO a ha C hC (smooth_compact_carrier L0) (smooth_compact_is_compact L0)
  (@smooth_compact_in_domain R X N hN A L0).
exists d; split=>// e he hed.
have hCentre:C e a.
  apply:(@hCapture e he hed a); right; reflexivity.
apply:(@distribution_constant_density_action R X Y NY hNY YD ed DN hYD
  (@euclidean_lebesgue_measure R n) (value f) v (g e) (g e a) (T (Q e f)) hVector).
- move=>x hx.
  apply:(@hConst e he a x hCentre).
  apply:(@hCapture e he hed x); left.
  exact:(@smooth_function_nonzero_in_support R X Y N hN (fun _=>True) DT value f x Logic.I hx).
- exact:(@hAction e he f).
Qed.
End InnerConstantIntegralEvaluation.
