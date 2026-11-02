(** Supporting Federer (1969), 2.10.46, p. 204: the projection-wise cylinder
    formula in Freilich (1950), Theorem 4.5, Parts 1–5, pp. 242–247. Adapted
    orthogonal coordinates reduce the actual multiplicity integral to the
    affine cylinder Fubini calculation. A finite transverse multiplicity
    integral discharges the exceptional-fibre obligation, including a null
    scalar factor. Averaging these projection-wise identities is a separate
    remaining step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanLebesgueDimensions
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionChartUP
  ScalarBlockMeasureBijection LineCylinderProjectionCoordinates EuclideanRectangleBorel
  TopologicalBorel ContinuousBorelPreimages MetricProductRectangles
  ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureBijectionUP MeasureBijectionLaws MeasureBijectionTotalIntegral ProductMeasure
  CountablyMeasurableUP CountablyMeasurableNullModification CountablyMeasurableProduct CountablyMeasurableFunctions LebesgueScalarMeasure
  MappingMultiplicity ProjectionMultiplicityIntegral BijectionPrecompositionMultiplicity
  BijectionPostcompositionMultiplicity FiniteProjectionFibres AffineCylinderProductIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [line_cylinder_borel]: supporting Borel
    domain for the cylinder in 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, p. 240,
    treats analytic factors. This preparatory statement uses
    Borel factors, sufficient before completion and exhaustion. *)
Lemma line_cylinder_borel (R : realType) n
    (T : set (real_line_metric R))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  borel_set T -> borel_set V ->
  borel_set ((fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)) @` (T `*` V)).
Proof.
move=> hT hV.
have he : (@euclidean_one_embed R) @` T=(@euclidean_one_project R) @^-1` T.
  apply/seteqP; split=> x.
  - move=> [t ht <-]; by rewrite /= euclidean_one_embedK.
  - move=> hx; exists (euclidean_one_project x)=> //; exact: euclidean_one_projectK.
have hE : borel_set ((@euclidean_one_embed R) @` T).
  rewrite he; exact (@continuous_borel_preimage
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R 1)]
    [the topologicalType of real_line_metric R] (@euclidean_one_project R)
    (@euclidean_one_project_continuous R) T hT).
have hs : (fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)) @` (T `*` V)=
    metric_product_rectangle (fun z=>(@euclidean_block_split R 1 n z).1)
      (fun z=>(@euclidean_block_split R 1 n z).2) ((@euclidean_one_embed R) @` T) V.
  apply/seteqP; split=> x.
  - move=> [[t y] [ht hy] <-].
    change (((@euclidean_one_embed R) @` T)
      (@euclidean_block_split R 1 n (@euclidean_block_join R 1 n (euclidean_one_embed t,y))).1 /\
      V (@euclidean_block_split R 1 n (@euclidean_block_join R 1 n (euclidean_one_embed t,y))).2).
    rewrite euclidean_block_joinK /=.
    split=> //; by exists t.
  - move=> [[t ht heq] hy]; exists (t,(@euclidean_block_split R 1 n x).2); first by split.
    rewrite /= heq -surjective_pairing; exact: euclidean_block_splitK.
rewrite hs; exact: euclidean_rectangle_borel hE hV.
Qed.

(** Source for [line_cylinder_projection_integral_value]:
    supporting projection-wise formula for 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Part 5, p. 247,
    after Parts 1–4, pp. 242–247. The scalar factor
    has finite length ell and the transverse projection integral
    has finite value r. A nonzero axis projection is explicit;
    its exceptional null set is not assumed away here. *)
Theorem line_cylinder_projection_integral_value (R : realType) n k
    (F : orthogonal_projection_metric_space R (1+n) (1+k))
    (Q : orthogonal_projection_metric_space R n k)
    (p : {linear R_n R (1+k) -> R_n R k})
    (c d : {linear R_n R (1+k) -> R_n R (1+k)})
    (T : set (real_line_metric R))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) (ell r : R) :
  is_orthogonal_projection_chart p c d ->
  (forall u y, p (euclidean_projection_linear F (@euclidean_block_join R 1 n (u,y)))=
    euclidean_projection_linear Q y) ->
  c (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0))) (lshift k ord0)!=0%R ->
  borel_set T -> borel_set V -> lebesgue_scalar_measure T=ell%:E ->
  projection_multiplicity_integral V Q=r%:E ->
  projection_multiplicity_integral
    ((fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)) @` (T `*` V)) F=
    (`|c (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0))) (lshift k ord0)|*ell*r)%R%:E.
Proof.
move=> hc hfactor ha hT hV hell hr.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R k).
pose U z := @euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2).
pose Ui z := (euclidean_one_project (@euclidean_block_split R 1 n z).1,
  (@euclidean_block_split R 1 n z).2).
pose S := U @` (T `*` V).
pose K z := (euclidean_one_project (@euclidean_block_split R 1 k (c z)).1,
  (@euclidean_block_split R 1 k (c z)).2).
pose D z := d (@euclidean_block_join R 1 k (euclidean_one_embed z.1,z.2)).
pose f := euclidean_projection_linear F.
pose q := euclidean_projection_linear Q.
pose h (z : R*X) := K (f (U z)).
pose a := c (f (@coordinate_basis R (1+n) (lshift n ord0))) (lshift k ord0).
pose b y := c (f (@euclidean_block_join R 1 n (0%R,y))) (lshift k ord0).
have hU := scalar_block_measure_bijection R n.
have hK := scalar_projection_chart_measure_bijection hc.
have hform t x : h (t,x)=((a*t+b x)%R,q x).
  have he := congr1 (fun z=>(euclidean_one_project (@euclidean_block_split R 1 k z).1,
    (@euclidean_block_split R 1 k z).2))
    (line_cylinder_projection_coordinates hc hfactor t x).
  rewrite euclidean_block_joinK /= euclidean_one_embedK in he.
  exact he.
have hcount z : @mapping_multiplicity R [the choiceType of (R*X)%type] (R*Y)%type h (T `*` V) z=
    @mapping_multiplicity R [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+n))]
      [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+k))] f S (D z).
  rewrite (@bijective_precomposition_multiplicity R [the choiceType of (R*X)%type]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+n))]
    (R*Y)%type U Ui (fun x=>K (f x)) (T `*` V) z
    (measure_bijection_inverse_cancel hU) (measure_bijection_cancel hU)).
  by rewrite /mapping_multiplicity (bijective_postcomposition_fibre f S z
    (measure_bijection_cancel hK) (measure_bijection_inverse_cancel hK)).
have hS : borel_set S := line_cylinder_borel hT hV.
have hi := projection_multiplicity_integral_specification F hS.
have ht := @measure_bijection_total_nonnegative_integral R (R*Y)%type
  [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+k))]
  (product_measure (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R k))
  (@euclidean_lebesgue_measure R (1+k))
  (product_measure_is_measure (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R k))
  (euclidean_lebesgue_is_measure R (1+k)) D K
  (fun y=>(@mapping_multiplicity R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+n))]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+k))] f S y : extended_real_line R))
  (projection_multiplicity_integral S F) (measure_bijection_inverse hK)
  (fun y=>@mapping_multiplicity_nonnegative R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+n))]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R (1+k))] f S y) hi.
have hj : is_measure_integral
    (product_measure (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R k))
    (partial_function_total (fun z=>(@mapping_multiplicity R [the choiceType of (R*X)%type]
      (R*Y)%type h (T `*` V) z : extended_real_line R))) (projection_multiplicity_integral S F).
  apply: (@measure_integral_graph_equivalent R (R*Y)%type _ _ _ _ _ ht)=> z w.
  change (mapping_multiplicity R f S (D z)=w <-> mapping_multiplicity R h (T `*` V) z=w).
  by rewrite hcount.
have hfinite := @finite_projection_integral_almost_finite_fibres R n k V Q hV ltac:(by rewrite hr ltry).
have hq := projection_multiplicity_integral_specification Q hV; rewrite hr in hq.
have hcm := @countably_measurable_function_on_countable_source R (R*Y)%type (extended_real_line R)
  _ (product_measure_is_measure (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R k)) 0 _
  (@extended_real_zero_closed R)
  (product_whole_countably_measurable (lebesgue_scalar_is_measure R)
    (euclidean_lebesgue_is_measure R k) (lebesgue_scalar_countably_measurable R)
    (euclidean_lebesgue_countably_measurable R k)) hj.1.
exact: (@affine_cylinder_product_integral_value R [the choiceType of X] [the choiceType of Y]
  (@euclidean_lebesgue_measure R k) (euclidean_lebesgue_is_measure R k)
  h q a ell r b T V (projection_multiplicity_integral S F) ha hform hT hell hfinite hq hj hcm).
Qed.
