(** Federer (1969), 3.2.10, p. 248: supporting
    measurable scalar functions of the actual differential.
    Apply the Borel graph statement of 3.1.1, p. 211,
    and Rademacher without assigning default derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness NormMetric NormMetricScaleContinuity
  NormClassOneUP NormClassZeroWhole NormDifferentialUP NormDifferential
  EuclideanHomOperator HomSpaceNormTopology ContinuousOperatorUP ContinuousOperatorNorm
  NormDifferentialBorelTests MetricProductBackground TopologicalProductMaps
  TopologicalBorel ContinuousBorelPreimages InnerOwnNormTopology
  RealMetricBackground PartialFunctionUP PartialFunctionPostcomposition
  EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP MeasurableFunctionUP LipschitzUP Rademacher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_differential_observable]: a scalar
    expression in Dv in Federer 3.2.10, p. 248,
    represented by postcomposition of the existing opaque
    differential. Its domain is exactly the differential domain. *)
Definition euclidean_differential_observable (R:realType) m n
    (f:R_n R m->R_n R n) (h:Hom (R_n R m) (R_n R n)->R):=
  partial_function_postcompose
    (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f) h.

(** Source for [euclidean_differential_observable_graph]:
    supporting exact-graph interpretation of the differential
    expressions in Federer 3.2.10, p. 248. A value
    requires an actual first-order differential witness. *)
Lemma euclidean_differential_observable_graph (R:realType) m n
    (f:R_n R m->R_n R n) (h:Hom (R_n R m) (R_n R n)->R) a r:
  partial_function_graph (euclidean_differential_observable f h) a r <->
  exists D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f a D /\ h D=r.
Proof.
split.
- move=>[D [hD he]]; exists D; split; last exact he.
  exact ((norm_differential_graph (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f a D).1 hD).
- move=>[D [hD he]]; exists D; split; last exact he.
  exact ((norm_differential_graph (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f a D).2 hD).
Qed.

(** Source for [euclidean_differential_observable_borel]: the
    measurable differential expressions needed for Fubini in
    Federer 3.2.10, p. 248. Supporting Borel preimages
    follow from 3.1.1, p. 211, for every continuous
    scalar observable and continuous f, on its exact domain. *)
Theorem euclidean_differential_observable_borel (R:realType) m n
    (f:R_n R m->R_n R n) (h:Hom (R_n R m) (R_n R n)->R):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (h L:real_line_metric R)) ->
  forall V:set (real_line_metric R),borel_set V ->
    @borel_set [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))]
      (partial_function_preimage (euclidean_differential_observable f h) V).
Proof.
move=>hf hh V hV.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose ev:=hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))).
pose hZ:=@euclidean_hom_operator_space R m n.
pose E:=real_norm_metric_space hNX.
pose T:=real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose P:=metric_product E T.
pose C:set P:=fun p=>V (h p.2).
have hC:borel_set C.
  apply:(continuous_borel_preimage _ hV)=>p.
  exact (continuous_comp (@second_projection_continuous E T p) (hh p.2)).
have [q [b hb]]:=@hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have hTest:=@norm_differential_borel_domain_test R (R_n R m) (R_n R n)
  (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev (@euclidean_operator_norm R m n)
  hZ m (@coordinate_basis R m) (@coordinate_basisP R m) q b hb setT f hf C hC.
have he:[set a:E|exists D,has_norm_differential NX NY setT f a (ev D) /\ C (a,D)]=
    partial_function_preimage (euclidean_differential_observable f h) V.
  apply/seteqP; split=>a.
  - move=>[D [hD hVal]]; exists (h D); split; last exact hVal.
    apply:(euclidean_differential_observable_graph f h a _).2; exists D; by split.
  - move=>[r [hr hVr]]; have [D [hD hDr]]:=(euclidean_differential_observable_graph f h a r).1 hr.
    exists D; split; first exact hD; by rewrite /C /= hDr.
by rewrite he in hTest.
Qed.

(** Source for [euclidean_differential_observable_measurable]:
    scalar differential expressions in Federer 3.2.10, p. 248,
    are Lebesgue measurable when f is Lipschitz and the
    expression is continuous in its differential. Rademacher supplies
    the conull actual domain rather than a default extension. *)
Theorem euclidean_differential_observable_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (h:Hom (R_n R m) (R_n R n)->R):
  is_metric_lipschitz setT f ->
  continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (h L:real_line_metric R)) ->
  @is_measure_measurable_function R _ [the topologicalType of real_line_metric R]
    (@euclidean_lebesgue_measure R m) (euclidean_differential_observable f h).
Proof.
move=>hLip hh; pose hm:=euclidean_lebesgue_is_measure R m.
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
- apply:(@measure_almost_everywhere_mono R _ _ hm _ _ _ (federer_3_1_6 hLip))=>a [D hD].
  exists (h D); apply:(euclidean_differential_observable_graph f h a _).2.
  exists D; by split.
- move=>V hV; have hB:=euclidean_differential_observable_borel hZero hh (open_borel_set hV).
  apply:(@borel_regular_borel_measurable R _ _ hm (euclidean_lebesgue_borel_regular R m)).
  exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hB).
Qed.
