(** Federer (1969), 3.2.33, p. 270: scalar
    continuity and measurability of the smooth density psi. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import RealMetricBackground RealNormUP NormClassOneUP PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP LebesgueScalarMeasure BorelRegularMeasureUP
  TopologicalBorel MeasurableRealEmbedding ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_class_zero_continuous]: supporting
    the integrand in g(t)= integral from zero to t of psi
    in Federer 3.2.33, p. 270. The abstract absolute-
    norm continuity law gives the usual scalar topology;
    no external calculus fact is used. *)
Lemma scalar_class_zero_continuous (R:realType) (f:R->R):
  norm_class_zero (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (fun _=>True) f ->
  continuous (fun t:real_line_metric R=>(f t:real_line_metric R)).
Proof.
move=>hf a U hU.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (f a:real_line_metric R) U) hU.
have [d [hd hClose]]:=(hf a Logic.I).2 e he.
apply:(proj2 (metricType_numDomainType.nbhs_mdistP (a:real_line_metric R) _)); exists d=>// t ht.
apply:hBall.
have hSmall:`|t-a|<d.
  change (is_true (mdist (a:real_line_metric R) t<d)) in ht.
  by rewrite real_line_metric_distanceE distrC in ht.
have hValue:=hClose (t-a) Logic.I hSmall.
have hEq:a+(t-a)= t by ring.
rewrite hEq in hValue.
change (is_true (`|f a-f t|<e)).
by rewrite distrC.
Qed.

(** Source for [scalar_class_zero_extended_measurable]: supporting
    existence of all bounded interval integrals defining g
    in Federer 3.2.33, p. 270. Actual scalar continuity,
    the finite extended-real inclusion and Borel regularity
    give measurability before any integral is chosen. *)
Lemma scalar_class_zero_extended_measurable (R:realType) (f:R->R):
  norm_class_zero (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (fun _=>True) f ->
  is_measure_measurable_function (@lebesgue_scalar_measure R)
    (partial_function_total (fun t:real_line_metric R=>((f t)%:E:extended_real_line R))).
Proof.
move=>hf.
have hContinuous:=scalar_class_zero_continuous hf.
have hC:continuous (fun t:real_line_metric R=>((f t)%:E:extended_real_line R)).
  move=>t; exact:(continuous_comp (hContinuous t) (@real_extended_embedding_continuous R (f t))).
constructor.
- rewrite partial_function_total_domain; exact:(measure_almost_everywhere_true (lebesgue_scalar_is_measure R)).
- move=>U hU; rewrite partial_function_total_preimage.
  apply:(@borel_regular_borel_measurable R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  apply:open_borel_set; apply:open_comp=>// t _; exact:hC.
Qed.
