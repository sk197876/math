(** Federer (1969), 3.3.13, pp. 297–298: actual positive atoms,
    unit interval and nonmeasurable source for the COMPLETE theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanOpenUnitCube
  EuclideanUnitCubeRectifiable EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanHausdorffLebesgue EuclideanMetricCompleteness EuclideanMetricSeparability
  HausdorffMeasure IntegralGeometricMeasure StructureHausdorffIntegralGeometric
  RectifiableSetUP EuclideanLipschitzRectifiableImage LipschitzUP PartialFunctionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  BernsteinNonmeasurableSubset BorelRegularMeasureUP TopologicalBorel
  PositiveClosedSubsets ApproximateDifferentialAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_complete_hausdorff_conclusion]: regression
    notation for the COMPLETE conclusion of Federer 3.3.13, pp.297–298.
    Retain the original Borel/pure decomposition and BOTH directions
    of actual Hausdorff/integral-geometric equality iff rectifiability. *)
Definition structure_complete_hausdorff_conclusion (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):Prop:=
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  let I:=@integral_geometric_measure R n m hmn t in
  (exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable H m (E `\` B) /\I (E `\` B)=0) /\
  (H E=I E <->is_measure_m_rectifiable H m E).

(** Source for [structure_complete_unit_cube]: actual regression
    support for COMPLETE Federer 3.3.13, pp.297–298. Every original
    unit cube has Hausdorff mass one; its actual rectifiability and
    the complete theorem give integral-geometric mass one for every
    printed exponent, including infinity and zero dimensions. *)
Lemma structure_complete_unit_cube (R:realType) m:
  let E:=@euclidean_open_unit_cube R m in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m in
  H E= 1%E /\forall t: \bar R,(1<=t)%E ->
    structure_complete_hausdorff_conclusion (leqnn m) E t /\
    @integral_geometric_measure R m m (leqnn m) t E= 1%E.
Proof.
cbn zeta.
have [hRect [_ hMass]]:=euclidean_open_unit_cube_measure_rectifiable R m.
split; first exact:hMass.
move=>t ht.
have hFinite:(@hausdorff_measure R
  (inner_metric_space (@euclidean_inner_productP R m)) m (@euclidean_open_unit_cube R m)< +oo)%E.
  by rewrite hMass ltry.
have hFull:=@federer_3_3_13 R m m (leqnn m) (@euclidean_open_unit_cube R m) t hFinite ht.
split; first exact:hFull.
rewrite -hMass; exact:esym (hFull.2.2 hRect).
Qed.

(** Source for [structure_hausdorff_positive_zero_cube]: actual nonempty
    R^0 unit cube of Hausdorff mass one in COMPLETE Federer 3.3.13,
    pp.297–298. Keep every exponent, actual integral-geometric atom
    and both directions of the original equality criterion. *)
Example structure_hausdorff_positive_zero_cube (R:realType):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0
    (@euclidean_open_unit_cube R 0)= 1%E /\
  forall t: \bar R,(1<=t)%E ->
    structure_complete_hausdorff_conclusion (leqnn 0) (@euclidean_open_unit_cube R 0) t /\
    @integral_geometric_measure R 0 0 (leqnn 0) t (@euclidean_open_unit_cube R 0)= 1%E.
Proof. exact:structure_complete_unit_cube. Qed.

(** Source for [structure_hausdorff_positive_unit_interval]: actual
    original open unit interval of Hausdorff mass one in COMPLETE
    Federer 3.3.13, pp.297–298. Every printed exponent has actual
    integral-geometric mass one, and the full decomposition/equivalence
    is retained rather than replaced by this computed equality. *)
Example structure_hausdorff_positive_unit_interval (R:realType):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1
    (@euclidean_open_unit_cube R 1)= 1%E /\
  forall t: \bar R,(1<=t)%E ->
    structure_complete_hausdorff_conclusion (leqnn 1) (@euclidean_open_unit_cube R 1) t /\
    @integral_geometric_measure R 1 1 (leqnn 1) t (@euclidean_open_unit_cube R 1)= 1%E.
Proof. exact:structure_complete_unit_cube. Qed.

(** Source for [structure_hausdorff_original_nonmeasurable_source]: an
    ACTUAL nonmeasurable positive finite-mass line subset of the original
    unit interval in COMPLETE Federer 3.3.13, pp.297–298. Actual 2.2.4
    supplies the original source; no measurable hull replaces it in
    either the decomposition or the equality criterion. *)
Example structure_hausdorff_original_nonmeasurable_source (R:realType):
  exists E:set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) E /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 E< +oo)%E /\
    forall t: \bar R,(1<=t)%E ->
      structure_complete_hausdorff_conclusion (leqnn 1) E t /\
      @integral_geometric_measure R 1 1 (leqnn 1) t E=
        @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose L:=@euclidean_lebesgue_measure R 1.
pose H:=@hausdorff_measure R [the metricType R of X] 1.
pose A:=@euclidean_open_unit_cube R 1.
have hL:=euclidean_lebesgue_is_measure R 1.
have hMass:L A= 1%E:=euclidean_unit_cube R 1.
have hPositive:(0<L A)%E by rewrite hMass lte_fin ltr01.
have hFinite:(L A< +oo)%E by rewrite hMass ltry.
have [E [hEA hNot]]:=@borel_regular_nonmeasurable_subset R [the metricType R of X] L hL
  (euclidean_lebesgue_borel_regular R 1) A (@euclidean_metric_complete R 1)
  (@euclidean_metric_separable R 1) hPositive hFinite
  (fun x _=>@positive_euclidean_singleton_null R 0 x).
have hEPositive:(0<L E)%E.
  rewrite lt_neqAle (measure_nonnegative hL E) andbT; apply/negP=>/eqP hZero.
  apply:hNot; exact:(@measure_null_measurable R [the choiceType of X] L hL E (esym hZero)).
have hAtMost:(L E<=1)%E by rewrite -hMass; exact:(@measure_mono R _ L hL _ _ hEA).
have hEFinite:(L E< +oo)%E:=le_lt_trans hAtMost (ltry _).
have hHE:H E=L E:=(euclidean_hausdorff_spherical_lebesgue E).1.
have hIdentity:@is_metric_lipschitz R [the metricType R of X] [the metricType R of X] E (@id X).
  exists 1; split; first exact:ltr01.
  split; first exact:ler01; by move=>x y _ _; rewrite mul1r.
have hCount:=euclidean_lipschitz_image_countably_rectifiable hIdentity.
rewrite image_id in hCount.
have hRect:is_measure_m_rectifiable H 1 E.
  split; last by rewrite hHE.
  split; first exact:hausdorff_measure_is_measure.
  exists E; split; first exact:hCount.
  rewrite /measure_almost_included setDv; exact:measure_empty (@hausdorff_measure_is_measure R [the metricType R of X] 1).
rewrite /H in hHE.
exists E; split; first exact:hNot.
split; first by rewrite hHE; apply/andP; split.
move=>t ht.
have hFull:=@federer_3_3_13 R 1 1 (leqnn 1) E t (ltac:(by rewrite hHE)) ht.
split; first exact:hFull.
exact:esym (hFull.2.2 hRect).
Qed.
