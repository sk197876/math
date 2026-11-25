(** Supporting the further slicing identities in Federer (1969), 2.10.16, p.
    178: replace a Suslin source by a Borel hull of the same exponent-one
    projection cost and no larger diameter. This is supporting
    infrastructure, not a separate claim printed there. A Borel hull of the
    incidence set is pulled back uniformly to all projections by Borel
    separation, 2.2.10, pp. 66–67. Intersect with the source closure to
    retain the diameter, as in 2.10.2(1), p. 171. They do not state this
    combined hull. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanLebesgueDimensions OrthogonalProjectionProbability ProjectionBeta
  ProjectedVolumeIncidence ProjectionIncidenceMeasure IntegralGeometricGauge
  MetricProductBackground MetricProductCompleteness MetricProductSeparability
  BorelRegularMeasureUP ProductMeasure ProductBorelRegularity
  SuslinSetUP SuslinPreimages BorelClosedProjection BorelImageMeasurability
  SuslinImageSeparation BorelSeparation TopologicalBorel BorelFamilyBasic BorelFunctionBasic
  TopologicalProductMaps CompleteMetricUP MetricDiameter MetricDiameterClosure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_projection_incidence_hull]: abstract laws of
    the supporting Borel replacement used for 2.10.16, p. 178.
    It contains S, preserves its actual incidence product measure,
    and does not enlarge its diameter. Existence is proved below. *)
Definition is_projection_incidence_hull (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (S C : set (inner_metric_space (@euclidean_inner_productP R n))) :=
  borel_set C /\ S `<=` C /\
  @projected_incidence_measure R n m hmn C=@projected_incidence_measure R n m hmn S /\
  extended_metric_diameter C<=extended_metric_diameter S.

(** Source for [projection_incidence_hull_gauge_one]: supporting
    cost consequence of the hull laws for 2.10.16, p. 178.
    The exponent-one gauge is the actual incidence measure
    divided by positive beta_1. Infinite costs are retained. *)
Lemma projection_incidence_hull_gauge_one (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (S C : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> is_projection_incidence_hull hmn S C ->
  @integral_geometric_gauge R n m hmn 1 C=@integral_geometric_gauge R n m hmn 1 S.
Proof.
move=> hS [hC [hSC [he hdiam]]].
have hC' := metric_borel_suslin hC.
have hbeta := @projection_beta_positive R n m hmn 1 (lexx _).
have hne : @projection_beta R n m hmn 1!=0%R by rewrite gt_eqF.
have hh : (@projection_beta R n m hmn 1)%:E*@integral_geometric_gauge R n m hmn 1 C=
    (@projection_beta R n m hmn 1)%:E*@integral_geometric_gauge R n m hmn 1 S.
  by rewrite (@integral_geometric_one_gauge_incidence R n m hmn C hC')
    (@integral_geometric_one_gauge_incidence R n m hmn S hS) he.
have hc : forall a b : \bar R,
    (@projection_beta R n m hmn 1)%:E*a=(@projection_beta R n m hmn 1)%:E*b -> a=b.
  move=> a b heq.
  have hi := congr1 (fun z => ((@projection_beta R n m hmn 1)^-1)%:E*z) heq.
  by rewrite !muleA -!EFinM (mulVf hne) !mul1e in hi.
exact: hc hh.
Qed.

(** Source for [suslin_projection_incidence_hull_exists]: proved
    Borel replacement for 2.10.16, p. 178. Separate S from
    the Suslin set of points having some projected incidence
    outside a product-measure Borel hull. The separator's closure
    restriction preserves cost and diameter, including infinite values. *)
Theorem suslin_projection_incidence_hull_exists (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> exists C, is_projection_incidence_hull hmn S C.
Proof.
move=> hS.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := orthogonal_projection_metric_space R n m.
pose T := [the metricType R of metric_product E P].
pose W := [the metricType R of metric_product Y P].
pose mu := product_measure (@euclidean_lebesgue_is_measure R m) (@theta_star_is_measure R n m hmn).
have hm := product_measure_is_measure (@euclidean_lebesgue_is_measure R m) (@theta_star_is_measure R n m hmn).
have [B [hIB [hB heB]]] := @product_measure_borel_hull R Y P
  (@euclidean_lebesgue_measure R m) (@orthogonal_projection_probability R n m hmn)
  (@euclidean_lebesgue_is_measure R m) (@theta_star_is_measure R n m hmn)
  (@euclidean_lebesgue_borel_regular R m) (@theta_star_borel_regular R n m hmn)
  (projection_incidence (m:=m) S).
pose F (z : T) : W := (euclidean_projection_linear z.2 z.1,z.2).
have hF : continuous F.
  apply: topological_pair_continuous; last exact: second_projection_continuous.
  have hs : continuous (fun z : T => (z.2,z.1)).
    apply: topological_pair_continuous.
    - exact: second_projection_continuous.
    - exact: first_projection_continuous.
  move=> z; exact: continuous_comp (hs z)
    (@euclidean_projection_evaluation_continuous R n m (z.2,z.1)).
pose D := F @^-1` (~` B).
have hD : borel_set D.
  exact (@borel_function_preimage T W F (continuous_borel_function hF) (~` B) (borel_set_complement hB)).
pose Bad := (@fst E P) @` D.
have hT : is_complete_metric_space T.
  exact: complete_metric_product (@euclidean_metric_complete R n) (@orthogonal_projection_metric_complete R n m).
have hsepT : exists H : set T, countable H /\ dense H.
  exact: separable_metric_product (euclidean_metric_separable R n) (orthogonal_projection_metric_separable R n m).
have hBad : is_suslin_set R Bad.
  exact: (@continuous_suslin_image R T E (@fst E P) D hT hsepT
    (@metric_hausdorff R E) (@first_projection_continuous E P) (metric_borel_suslin hD)).
have hdis : S `&` Bad=set0.
  apply/seteqP; split=> // x [hx [z hz hzx]].
  have hSrc : S z.1 by rewrite hzx.
  have hinc : projection_incidence (m:=m) S (F z) by exists z.1; split.
  exfalso; exact: hz (hIB _ hinc).
have hdis' : (id @` S) `&` (id @` Bad)=set0 by rewrite !image_id.
have hsep := @disjoint_suslin_images_borel_separated R E E id S Bad
  (@euclidean_metric_complete R n) (euclidean_metric_separable R n) (@metric_hausdorff R E)
  (fun x => cvg_id) hS hBad hdis'.
rewrite !image_id in hsep.
have [C [hC [hSC hBadC]]] := (borel_separated_one_separator S Bad).1 hsep.
have hincC : projection_incidence (m:=m) C `<=` B.
  move=> [y p] [x [hx hxy]]; apply: contrapT=> hn.
  have hbad : Bad x.
    exists (x,p); last by [].
    change (~B (euclidean_projection_linear p x,p)).
    by rewrite -hxy.
  exact: (hBadC x hbad) hx.
have hCM : @projected_incidence_measure R n m hmn C<=@projected_incidence_measure R n m hmn S.
  change (mu (projection_incidence (m:=m) C)<=mu (projection_incidence (m:=m) S)).
  have he : mu (projection_incidence (m:=m) S)=mu B := heB.
  rewrite he; exact (@measure_mono R W mu hm (projection_incidence (m:=m) C) B hincC).
pose H := C `&` closure S.
have hH : borel_set H.
  apply: (@borel_family_binary_intersection E setT _ (borel_sets_family E))=> //.
  exact: closed_borel_set (@closed_closure E S).
have hSH : S `<=` H by move=> x hx; split; [exact: hSC x hx|exact: subset_closure hx].
have hHC : H `<=` C by move=> x [].
have hmeasure : @projected_incidence_measure R n m hmn H=@projected_incidence_measure R n m hmn S.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact (le_trans (@measure_mono R E _ (@projected_incidence_is_measure R n m hmn) H C hHC) hCM).
  - exact (@measure_mono R E _ (@projected_incidence_is_measure R n m hmn) S H hSH).
have hdiam : extended_metric_diameter H<=extended_metric_diameter S.
  rewrite -(extended_metric_diameter_closure S).
  apply: extended_metric_diameter_mono; by move=> x [].
exists H; by split=> //; split=> //; split.
Qed.
