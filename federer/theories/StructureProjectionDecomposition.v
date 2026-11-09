(** Federer (1969), 3.3.12, p. 297: the complete original
    Borel rectifiable/pure decomposition with projected-null remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions OrthogonalProjectionProbability StructureConeUP
  StructureProjectionConditions StructurePureProjectionNull StructurePureStructure
  RectifiableSetUP RectifiablePureDecomposition SuslinSetUP BorelClosedProjection
  BorelSuslinImages TopologicalBorel MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_3_12]: COMPLETE Federer 3.3.12, p. 297.
    Original Suslin E has finite phi outer mass; almost every ORIGINAL
    projection satisfies both original (I) and (II). There exists a
    countably m rectifiable Borel R such that ORIGINAL E minus R is
    purely (phi,m) unrectifiable and its ORIGINAL projected image is
    Lebesgue-null at almost every original projection. The standing phi
    need only measure closed sets. The actual 3.2.14 decomposition,
    actual 3.3.10 theorem, and every null-union and almost-everywhere
    premise are proved, rather than supplied as structure hypotheses. *)
Theorem federer_3_3_12 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->is_suslin_set R E ->phi E< +oo ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|structure_projection_preserves_null_subsets phi E p /\
      structure_projection_almost_finite_fibres E p] ->
  exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable phi m (E `\` B) /\
    measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
      [set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` (E `\` B))=0].
Proof.
move=>hStructure hE hFinite hProjections.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [B [hBorel [hRectifiable hPure]]]:=@rectifiable_pure_borel_decomposition R
  [the metricType R of X] phi m E hStructure.1 hFinite hStructure.2.
pose A:=E `\` B.
have hAE:A `<=` E by move=>x [hx _].
have hA:is_suslin_set R A.
  rewrite /A setDE; apply:suslin_binary_intersection; first exact:hE.
  apply:metric_borel_suslin; exact:borel_set_complement hBorel.
have hFiniteA:phi A< +oo:=le_lt_trans (@measure_mono R _ phi hStructure.1 _ _ hAE) hFinite.
have [_ [_ [_ hAlmost]]]:=@federer_3_3_10 R n m hmn phi A hStructure hPure hA hFiniteA.
have hTheta:=theta_star_is_measure R hmn.
have hBoth:=measure_almost_everywhere_and hTheta hProjections hAlmost.
exists B; split; first exact:hBorel.
split; first exact:hRectifiable.
split; first exact:hPure.
apply:(measure_almost_everywhere_mono hTheta _ hBoth).
move=>p [[hI hII] hOriginalNull].
exact:(@structure_pure_projection_null R n m hmn phi E A p
  hStructure hFiniteA hAE hI hII hOriginalNull).
Qed.
