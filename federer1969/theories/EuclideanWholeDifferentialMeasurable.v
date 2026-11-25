(** Federer (1969), 3.1.1, p. 211: the actual
    differential has a Borel graph on its domain. For a
    Lipschitz map Rademacher makes that domain conull.
    This support for 3.2.46, p. 282, retains
    the partial operator rather than choosing a derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness NormMetric
  NormMetricScaleContinuity NormClassOneUP NormClassZeroWhole NormDifferentialUP
  NormDifferential EuclideanHomOperator HomSpaceNormTopology ContinuousOperatorUP
  ContinuousOperatorNorm NormDifferentialBorelTests MetricProductBackground
  TopologicalProductMaps TopologicalBorel ContinuousBorelPreimages InnerOwnNormTopology
  PartialFunctionUP EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP MeasurableFunctionUP LipschitzUP Rademacher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_whole_differential_measurable]:
    measurability of the actual Hom-valued partial differential,
    3.1.1, p. 211, with its conull domain
    supplied by 3.1.6, pp. 216–217. This applies
    in all natural dimensions, including a zero source or target. *)
Theorem euclidean_whole_differential_measurable (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  is_metric_lipschitz setT f ->
  @is_measure_measurable_function R _
    [the topologicalType of real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)]
    (@euclidean_lebesgue_measure R m)
    (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f).
Proof.
move=> hLip.
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
pose ev := hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))).
pose hZ := @euclidean_hom_operator_space R m n.
pose E := real_norm_metric_space hNX.
pose T := real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose P := metric_product E T.
have hCont : continuous (fun x : E=>(f x : real_norm_metric_space hNY)).
  have [L [hL hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R _ _ _ L (ltW hL)).
  by move=> x y; exact:hBound.2 x y Logic.I Logic.I.
have hZero := @norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  NX NY hNX hNY f hCont.
constructor.
- apply: (@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R m)
    _ _ _ (federer_3_1_6 hLip))=> x [D hD].
  exists D; exact:(norm_differential_graph hNX hNY setT f x D).2 hD.
- move=> V hV.
  have hVt : @open T V.
    have hProof : @euclidean_operator_norm_is_norm R m n=continuous_operator_norm_is_norm hNY hZ := Prop_irrelevance _ _.
    rewrite /T -hProof; exact hV.
  pose C : set P := (fun z : P=>z.2) @^-1` V.
  have hC : borel_set C := @continuous_borel_preimage P T (fun z=>z.2)
    (@second_projection_continuous E T) V (open_borel_set hVt).
  have [q [b hb]] := @hom_space_finite_basis R (R_n R m) (R_n R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    n (@coordinate_basis R n) (@coordinate_basisP R n).
  have hTest := @norm_differential_borel_domain_test R (R_n R m) (R_n R n)
    (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev (@euclidean_operator_norm R m n)
    hZ m (@coordinate_basis R m) (@coordinate_basisP R m) q b hb setT f hZero C hC.
  have hEqual : [set a : E | exists D, has_norm_differential NX NY setT f a (ev D) /\ C (a,D)] =
      partial_function_preimage (norm_differential hNX hNY setT f) V.
    apply/seteqP; split=> a.
    + move=> [D [hD hValue]]; exists D; split; last exact hValue.
      exact:(norm_differential_graph hNX hNY setT f a D).2 hD.
    + move=> [D [hD hValue]]; exists D; split; last exact hValue.
      exact:(norm_differential_graph hNX hNY setT f a D).1 hD.
  rewrite hEqual in hTest.
  apply: (@borel_regular_borel_measurable R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_borel_regular R m)).
  exact:(inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hTest.
Qed.
