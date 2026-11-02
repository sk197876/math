(** Federer (1969), 3.1.4, p. 214: the full Euclidean
    statement, combining the proved scalar almost-everywhere theorem
    and the exact measurable approximate-partial interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates LinearBasis
  BasisInterpolation EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness EuclideanCoordinateTopology EuclideanLebesgueDimensions
  RealNormUP RealMetricBackground PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialFunctionPostcomposition
  ApproximatePartialDerivative ApproximatePartialCoordinates ApproximatePartialMeasurable
  ApproximateDifferentialUP ApproximateDifferential ApproximateDifferentialTargetCoordinates
  ScalarApproximateDifferentiability MeasureUP MeasureRestriction MeasureAlmostUP
  MeasureAlmostBasic MeasurableFunctionUP MeasurablePostcomposition
  BorelFunctionBasic MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_partial_target_coordinate]: scalar
    reduction in Federer 3.1.4, p. 214. A vector approximate
    partial gives each coordinate partial on the identical source.
    In target dimension zero there is no coordinate to assert. *)
Lemma approximate_partial_target_coordinate (R : realType) m n
    (A : set (R_n R m)) (f : R_n R m -> R_n R n)
    (i : 'I_m) (a : R_n R m) (v : R_n R n) (j : 'I_n) :
  partial_function_graph
    (approximate_partial_derivative
      (inner_norm_real_norm (@euclidean_inner_productP R n)) A f i) a v ->
  partial_function_graph
    (approximate_partial_derivative (scalar_absolute_value_norm R) A
      (fun x=>f x j) i) a (v j).
Proof.
case: n f v j=> [f v j|n f v j].
- by have := ltn_ord j; rewrite ltn0.
- move=> hv.
  apply: (approximate_partial_derivative_graph (scalar_absolute_value_norm R)
    A _ i a (v j)).2.
  exact: (@approximate_partial_positive_target_coordinates R m n A f a i v).1
    ((approximate_partial_derivative_graph
      (inner_norm_real_norm (@euclidean_inner_productP R n.+1)) A f i a v).1 hv) j.
Qed.

(** Source for [euclidean_approximate_differentiability_from_partials]:
    the last conclusion and displayed formula of Federer 3.1.4,
    p. 214, with proof on pp. 214–216. The source dimension
    is positive, in accordance with the nonempty punctured quotient
    used in 3.1.2, p. 212; every target dimension is included. *)
Theorem euclidean_approximate_differentiability_from_partials (R : realType) m n
    (f : R_n R m.+1 -> R_n R n) :
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m.+1)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (@euclidean_lebesgue_measure R m.+1) (partial_function_total f) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1)
    (\bigcap_i partial_function_domain
      (approximate_partial_derivative
        (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i))
    [set a | exists L : Hom (R_n R m.+1) (R_n R n),
      exists v : 'I_m.+1 -> R_n R n,
      partial_function_graph
        (approximate_differential
          (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f) a L /\
      (forall i, partial_function_graph
        (approximate_partial_derivative
          (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i) a (v i)) /\
      forall h, L h=\sum_(i<m.+1) h i *: v i].
Proof.
move=> hf.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose hm := euclidean_lebesgue_is_measure R m.+1.
pose hs := scalar_absolute_value_norm R.
pose hN := inner_norm_real_norm (@euclidean_inner_productP R n).
pose Aj (j : 'I_n) := \bigcap_i partial_function_domain
  (approximate_partial_derivative hs setT (fun x=>f x j) i).
pose Pj (j : 'I_n) := [set a | exists L : Hom (R_n R m.+1) [the lmodType R of R^o],
  has_approximate_differential (fun x : R^o=>`|x|) setT (fun x=>f x j) a L /\
  forall i : 'I_m.+1, partial_function_graph
    (approximate_partial_derivative hs setT (fun x=>f x j) i) a
      (L (@coordinate_basis R m.+1 i))].
have hscalar j : measure_almost_everywhere_on mu (Aj j) (Pj j).
  apply: scalar_approximate_differentiability_from_partials.
  have hpost := measurable_function_borel_postcomposition hm hf
    (continuous_borel_function (@euclidean_coordinate_continuous R n j)).
  apply: (measurable_function_graph_equivalent _ hpost)=> x y.
  by split=> [[z [<- <-]]|<-]; last (exists (f x); split).
have hcommon : measure_almost_everywhere mu
    (\bigcap_j [set a | Aj j a -> Pj j a]).
  apply: (measure_almost_everywhere_countable hm); first exact: countableP.
  move=> j _; exact: (measure_almost_everywhere_on_implication _ _ _).1 (hscalar j).
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono hm _ hcommon)=> a hcommonA ha.
have hex : forall i : 'I_m.+1, exists v,
    partial_function_graph (approximate_partial_derivative hN setT f i) a v.
  move=> i; exact: ha i Logic.I.
have [v hv] := choice hex.
pose L := hom_of_linear (basis_interpolation (@coordinate_basisP R m.+1) v).
have hL i : L (@coordinate_basis R m.+1 i)=v i.
  by rewrite /L hom_of_linearE basis_interpolationE.
have hc j : linear (fun h : R_n R m.+1 => (L h) j).
  by move=> c x y; rewrite (hom_linear L) !ffunE.
pose Lc j := @HomMap R (R_n R m.+1) [the lmodType R of R^o]
  (fun h=>(L h) j) (introT (asboolP _) (hc j)).
have hLc j : has_approximate_differential (fun x : R^o=>`|x|) setT
    (fun x=>f x j) a (Lc j).
  have haj : Aj j a.
    move=> i _; exists (v i j).
    exact: (@approximate_partial_target_coordinate R m.+1 n setT f i a (v i) j (hv i)).
  have [M [hM hMb]] := hcommonA j Logic.I haj.
  have he : M=Lc j.
    apply: hom_ext.
    apply: (basis_linear_ext (@coordinate_basisP R m.+1)
      (hom_as_linear M) (hom_as_linear (Lc j)))=> i.
    change (M (@coordinate_basis R m.+1 i)=(L (@coordinate_basis R m.+1 i)) j).
    rewrite hL.
    exact: partial_function_single_valued (hMb i)
      (@approximate_partial_target_coordinate R m.+1 n setT f i a (v i) j (hv i)).
  by rewrite -he.
exists L, v; split.
- apply: (approximate_differential_graph hN setT f a L).2.
  exact: (@approximate_differential_from_target_coordinates R m n f a L Lc
    (fun j h=>erefl _) hLc).
- split=> // h.
  rewrite -{1}(euclidean_coordinate_expansion h) linear_sum.
  apply: eq_bigr=> i _; rewrite linearZ.
  change (h i *: L (@coordinate_basis R m.+1 i)=h i *: v i).
  by rewrite hL.
Qed.

(** Source for [federer_3_1_4]: all three assertions of Federer
    3.1.4, p. 214: measurable partial domains, measurable
    partials for the restricted measure, and almost-everywhere
    approximate differentiability with the printed coordinate formula.
    The corrected weak variation threshold is taken from the erratum,
    p. 4, book p. 214, line 24. *)
Theorem federer_3_1_4 (R : realType) m n (f : R_n R m.+1 -> R_n R n) :
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m.+1)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (@euclidean_lebesgue_measure R m.+1) (partial_function_total f) ->
  (forall i : 'I_m.+1, measure_measurable (@euclidean_lebesgue_measure R m.+1)
    (partial_function_domain (approximate_partial_derivative
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i))) /\
  (forall i : 'I_m.+1, @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m.+1)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (measure_restrict (@euclidean_lebesgue_measure R m.+1)
      (partial_function_domain (approximate_partial_derivative
        (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i)))
    (approximate_partial_derivative
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i)) /\
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1)
    (\bigcap_i partial_function_domain
      (approximate_partial_derivative
        (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i))
    [set a | exists L : Hom (R_n R m.+1) (R_n R n),
      exists v : 'I_m.+1 -> R_n R n,
      partial_function_graph
        (approximate_differential
          (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f) a L /\
      (forall i, partial_function_graph
        (approximate_partial_derivative
          (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i) a (v i)) /\
      forall h, L h=\sum_(i<m.+1) h i *: v i].
Proof.
move=> hf.
have hfA : @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m.+1)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (@euclidean_lebesgue_measure R m.+1)
    (partial_function_source_restrict setT (partial_function_total f)).
  apply: (measurable_function_graph_equivalent _ hf)=> x y; by split=> [hy|[_ hy]].
split; first by move=> i; exact: euclidean_approximate_partial_domain_measurable i hfA.
split; first by move=> i; exact: euclidean_approximate_partial_measurable i hfA.
exact: euclidean_approximate_differentiability_from_partials hf.
Qed.
