(** Federer (1969), 3.2.25, p. 261: supporting
    measurable functions of the actual differential.
    Apply the Borel graph statement of 3.1.1, p. 211,
    and Rademacher without assigning default derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness NormMetric NormMetricScaleContinuity BorelFunctionUP BorelFunctionBasic
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

(** Source for [euclidean_differential_postcompose]: a vector
    expression in Dv in Federer 3.2.25, p. 261,
    represented by postcomposition of the existing opaque
    differential. Its domain is exactly the differential domain. *)
Definition euclidean_differential_postcompose (R:realType) m n
    (Y:topologicalType) (f:R_n R m->R_n R n) (h:Hom (R_n R m) (R_n R n)->Y):=
  partial_function_postcompose
    (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f) h.

(** Source for [euclidean_differential_postcompose_graph]:
    supporting exact-graph interpretation of the differential
    expressions in Federer 3.2.25, p. 261. A value
    requires an actual first-order differential witness. *)
Lemma euclidean_differential_postcompose_graph (R:realType) m n
    (Y:topologicalType) (f:R_n R m->R_n R n) (h:Hom (R_n R m) (R_n R n)->Y) a (r:Y):
  partial_function_graph (euclidean_differential_postcompose f h) a r <->
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

(** Source for [euclidean_differential_postcompose_borel]: the
    Borel differential expressions underlying the measurable tangent
    field of Federer 3.2.25, p. 261. The single-valued Borel
    differential graph of 3.1.1, p. 211, permits every Borel
    target expression, including normalized vector expressions. Its
    exact partial domain is retained; no default derivative field
    is supplied or assumed. *)
Theorem euclidean_differential_postcompose_borel (R:realType) m n
    (Y:topologicalType) (f:R_n R m->R_n R n) (h:Hom (R_n R m) (R_n R n)->Y):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  is_borel_function (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (h L:Y)) ->
  forall V:set Y,borel_set V ->
    @borel_set [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))]
      (partial_function_preimage (euclidean_differential_postcompose f h) V).
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
  have hProjection:continuous (fun p:P=>(p.2:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n))).
    move=>p; exact:(@second_projection_continuous E T p).
  exact:(continuous_borel_preimage hProjection (borel_function_preimage hh hV)).
have [q [b hb]]:=@hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have hTest:=@norm_differential_borel_domain_test R (R_n R m) (R_n R n)
  (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev (@euclidean_operator_norm R m n)
  hZ m (@coordinate_basis R m) (@coordinate_basisP R m) q b hb setT f hf C hC.
have he:[set a:E|exists D,has_norm_differential NX NY setT f a (ev D) /\ C (a,D)]=
    partial_function_preimage (euclidean_differential_postcompose f h) V.
  apply/seteqP; split=>a.
  - move=>[D [hD hVal]]; exists (h D); split; last exact hVal.
    apply:(euclidean_differential_postcompose_graph f h a _).2; exists D; by split.
  - move=>[r [hr hVr]]; have [D [hD hDr]]:=(euclidean_differential_postcompose_graph f h a r).1 hr.
    exists D; split; first exact hD; by rewrite /C /= hDr.
by rewrite he in hTest.
Qed.

