(** Federer (1969), 4.1.7, pp. 355–356:
    current products extend to measurable locally
    summable fields. This supporting measurability
    step is the earlier 2.3.2(4)–(5), p. 73,
    followed by the proved continuity of the
    actual bounded bilinear coefficient operation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses NormBoundedBilinearUP
  BoundedBilinearContinuity PartialFunctionUP PartialFunctionBasic PartialFunctionPair
  MeasureUP MeasurableFunctionUP MeasurablePairs MeasurablePostcomposition MeasurableGraphEquivalence
  BorelFunctionBasic CountableOpenBaseUP SeparableMetricBaseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measurable_bounded_bilinear_product]:
    two original norm-measurable fields have a
    norm-measurable bilinear product, supporting
    Federer 4.1.7, pp. 355–356. Separability
    of the two coefficient spaces supplies the
    countable factor bases; completeness and source
    finiteness are not required. *)
Theorem measurable_bounded_bilinear_product (R:realType) (X:choiceType)
    (A B C:lmodType R) (NA:A->R) (NB:B->R) (NC:C->R)
    (hNA:is_real_norm NA) (hNB:is_real_norm NB) (hNC:is_real_norm NC)
    (mu:set X->\bar R) (hm:is_measure mu)
    (F:A->B->C) (hF:norm_bounded_bilinear NA NB NC F)
    (f:X->A) (g:X->B):
  is_separable_normed_space hNA ->is_separable_normed_space hNB ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hNA))) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(g x:real_norm_metric_space hNB))) ->
  is_measure_measurable_function mu (partial_function_total
    (fun x=>(F (f x) (g x):real_norm_metric_space hNC))).
Proof.
move=>[DA [hDAC hDAD]] [DB [hDBC hDBD]] hf hg.
pose AM:=real_norm_metric_space hNA.
pose BM:=real_norm_metric_space hNB.
pose CM:=real_norm_metric_space hNC.
pose U:=@SeparableMetricBase.value R AM DA hDAC hDAD.
pose V:=@SeparableMetricBase.value R BM DB hDBC hDBD.
have hU:=@SeparableMetricBase.laws R AM DA hDAC hDAD.
have hV:=@SeparableMetricBase.laws R BM DB hDBC hDBD.
have hPair:=@measurable_partial_function_pair R X AM BM nat nat mu hm
  (partial_function_total (fun x=>(f x:AM))) (partial_function_total (fun x=>(g x:BM))) U V
  (countable_base_open hU) (countable_base_refines hU)
  (countable_base_open hV) (countable_base_refines hV) hf hg.
have hContinuous:continuous (fun p:AM*BM=>(F p.1 p.2:CM)).
  exact:(@bounded_bilinear_continuous_factors R A B C NA NB NC hNA hNB hNC F hF
    [the topologicalType of (AM*BM)%type] fst snd (fun p=>cvg_fst) (fun p=>cvg_snd)).
have hProduct:=@measurable_function_borel_postcomposition R X
  [the topologicalType of (AM*BM)%type] CM mu hm _
  (fun p:AM*BM=>(F p.1 p.2:CM)) hPair (continuous_borel_function hContinuous).
apply:(@measurable_function_graph_equivalent R X CM mu _ _ _ hProduct)=>x y; split.
- move=>[[u v] [[hu hv] hValue]].
  change (f x=u) in hu; change (g x=v) in hv.
  by rewrite -hu -hv in hValue.
- move=>hValue; exists (f x,g x); split; first by split.
  exact:hValue.
Qed.
