(** Federer (1969), 3.2.3, p. 243: Rademacher's
    theorem supplies the conull domain of the area integrand,
    and its Borel preimages give Lebesgue measurability. The
    Jacobian remains undefined off its differential domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormMetricScaleContinuity NormClassOneUP NormClassZeroWhole
  EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel MeasurableFunctionUP BorelFunctionBasic
  PartialFunctionUP PartialFunctionPostcomposition PartialZeroExtension MeasurablePostcomposition MeasurableRealEmbedding
  RealMetricBackground ExtendedRealOrderTopology PartialExtendedOrderLoci MeasurableZeroExtension ZeroExtensionNonnegative
  MeasureNonnegativeIntegral MeasureIntegralUP MeasureSubsetIntegral MeasureIntegral
  LipschitzUP Rademacher Jacobian EuclideanJacobianBorel InnerOwnNormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_top_jacobian_measurable]: the
    Lebesgue-measurable, conull Jacobian integrand used in
    Federer 3.2.3, p. 243, by 3.1.6 and the
    exact Borel graph of the differential. *)
Theorem euclidean_top_jacobian_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of real_line_metric R]
    (@euclidean_lebesgue_measure R m) (euclidean_jacobian m setT f).
Proof.
move=>hLip.
pose hm:=euclidean_lebesgue_is_measure R m.
have hCont:continuous (fun x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))=>
    (f x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))).
  have [L [hL hBound]]:=hLip.
  apply:(@metric_fixed_lipschitz_continuous R _ _ _ L (ltW hL)).
  by move=>x y; exact (hBound.2 x y Logic.I Logic.I).
have hZero:=@norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) f hCont.
constructor.
- apply:(@measure_almost_everywhere_mono R _ _ hm _ _ _ (federer_3_1_6 hLip))=>a ha.
  exact ((euclidean_jacobian_domain m setT f a).2 ha).
- move=>U hU.
  have hB:=euclidean_top_jacobian_borel_preimage hZero (open_borel_set hU).
  apply:(@borel_regular_borel_measurable R _ _ hm (euclidean_lebesgue_borel_regular R m)).
  exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hB).
Qed.

(** Source for [extended_euclidean_jacobian]: the finite
    nonnegative real Jacobian viewed as an extended integrand
    in Federer 3.2.3, p. 243. Postcomposition preserves
    precisely the original partial differential domain. *)
Definition extended_euclidean_jacobian (R:realType) m n
    (f:R_n R m->R_n R n):partial_function (R_n R m) (extended_real_line R):=
  partial_function_postcompose (euclidean_jacobian m setT f)
    (fun r:real_line_metric R=>(r%:E:extended_real_line R)).

(** Source for [extended_euclidean_jacobian_measurable]: the
    integrand of Federer 3.2.3, p. 243, with the
    extended integral's target topology and original partial
    Jacobian domain. *)
Lemma extended_euclidean_jacobian_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (extended_euclidean_jacobian f).
Proof.
move=>hLip.
apply:(@measurable_function_borel_postcomposition R _ [the topologicalType of real_line_metric R]
  (extended_real_line R) _ (euclidean_lebesgue_is_measure R m) _ _
  (euclidean_top_jacobian_measurable hLip)).
exact (continuous_borel_function (@real_extended_embedding_continuous R)).
Qed.

(** Source for [extended_euclidean_jacobian_nonnegative]: the
    nonnegativity of the norm Jacobian in the area integrand,
    Federer 3.2.3, p. 243, at every actual graph point. *)
Lemma extended_euclidean_jacobian_nonnegative (R:realType) m n
    (f:R_n R m->R_n R n) a j:
  partial_function_graph (extended_euclidean_jacobian f) a j -> 0<=j.
Proof.
move=>[r [hr <-]]; rewrite lee_fin; exact (euclidean_jacobian_nonnegative hr).
Qed.

(** Source for [euclidean_jacobian_subset_integrable]: the
    left area integral of Federer 3.2.3(1), p. 243,
    exists on every Lebesgue-measurable subset. It may be
    infinite; no finiteness of source measure is added. *)
Theorem euclidean_jacobian_subset_integrable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_subset_integrable (@euclidean_lebesgue_measure R m) A (extended_euclidean_jacobian f).
Proof.
move=>hLip hA.
pose hm:=euclidean_lebesgue_is_measure R m.
have hJ:=extended_euclidean_jacobian_measurable hLip.
have hPos:measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_extended_nonnegative_locus (extended_euclidean_jacobian f)).
  apply:(@measure_almost_everywhere_mono R _ _ hm _ _ _ (measurable_function_domain hJ)).
  move=>x [j hj]; exists j; split; first exact hj.
  exact (extended_euclidean_jacobian_nonnegative hj).
have hCut:=@measurable_zero_extension R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)] (extended_real_line R)
  (@euclidean_lebesgue_measure R m) hm 0 A (extended_euclidean_jacobian f) hA hJ.
apply:(@nonnegative_measurable_function_integrable R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) hm _ hCut).
exact (@zero_extension_nonnegative_almost R _ _ hm A (extended_euclidean_jacobian f) hPos).
Qed.
