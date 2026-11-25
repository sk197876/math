(** Federer (1969), 3.4.8(13), p. 336:
    transport a compact model through psi_lambda. The
    coordinate projection becomes the original prefix projection;
    orthogonal Hausdorff invariance transports the null remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric HomInner ExteriorIndices CoordinateProjection OrthogonalMaps OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure OrthogonalHausdorffImage MappingMultiplicity MappingChartMultiplicity
  EuclideanLebesgueDimensions ProjectionMultiplicityNullRemainder LipschitzUP LipschitzRectifiableImages RectifiableSetUP
  HausdorffMeasure MeasureAlmostUP MetricIsometricImageGeometry InnerNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_coordinate_model_transport]: the original
    inequalities N(p_lambda|psi_lambda(S_lambda),y)<=k_lambda
    outside a null set in 3.4.8(13), p. 336.
    Neither source measurability nor finite total mass is assumed. *)
Theorem orthogonal_coordinate_model_transport (R:realType) n m
    (lambda:Lambda n m)
    (psi:@orthogonal_group R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n))
    (P:Hom (R_n R n) (R_n R m)) (S Z:set (R_n R n)) (c: \bar R):
  (forall x,P x=@coordinate_projection R n m lambda (orthogonal_element_map psi x)) ->
  @compact (inner_metric_space (@euclidean_inner_productP R n)) S ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (S `\` Z)=0%E ->
  @is_countably_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m S ->
  (forall y,(@mapping_multiplicity R (inner_metric_space (@euclidean_inner_productP R n))
    (R_n R m) P Z y<=c)%E) ->
  let u:=orthogonal_element_map psi in
  @compact (inner_metric_space (@euclidean_inner_productP R n)) (u @` S) /\
  @is_countably_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m (u @` S) /\
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set y|(@mapping_multiplicity R (inner_metric_space (@euclidean_inner_productP R n))
      (R_n R m) (@coordinate_projection R n m lambda) (u @` S) y<=c)%E].
Proof.
move=>hProjection hCompact hNull hRect hCount u.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose p:=@coordinate_projection R n m lambda.
have hOrthogonal:=orthogonal_element_orthogonal psi.
have hInjective:=orthogonal_map_injective (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R n) hOrthogonal.
have hImageDifference:(u @` S) `\` (u @` Z)=u @` (S `\` Z).
  apply/seteqP;split.
  - move=>y [[x hx <-] hNot];exists x;last exact:erefl.
    split;first exact:hx.
    move=>hxZ;apply:hNot;by exists x.
  - move=>y [x [hx hNot] <-];split;first by exists x.
    move=>[z hz hSame];apply:hNot.
    have hEqual:z=x:=hInjective _ _ hSame;by rewrite -hEqual.
have hTransportNull:@hausdorff_measure R X m ((u @` S) `\` (u @` Z))=0%E.
  rewrite hImageDifference.
  exact:eq_trans (@hausdorff_orthogonal_image R n m (hom_as_linear u) (S `\` Z) hOrthogonal) hNull.
have hTransportCount y:(@mapping_multiplicity R X (R_n R m) p (u @` Z) y<=c)%E.
  have hChart:=@mapping_multiplicity_injective_chart R X X (R_n R m) Z u p y
    (fun x z _ _ hSame=>hInjective _ _ hSame).
  have hMaps:(fun x=>p (u x)) = P by apply:funext=>x;exact:esym (hProjection x).
  rewrite -hChart hMaps;exact:hCount y.
have hLip:=orthogonal_euclidean_lipschitz_one hOrthogonal.
have hDistance (x y:X):@mdist R X (u x) (u y)=mdist x y.
  by rewrite !inner_metric_distanceE -linearB
    (orthogonal_map_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) hOrthogonal).
have hContinuous:=@metric_isometric_map_continuous R X X u hDistance.
split.
- exact:(continuous_compact (continuous_subspaceT hContinuous) hCompact).
split.
- apply:(countably_hausdorff_rectifiable_lipschitz_image _ hRect).
  exists 1;split;first exact:ltr01.
  split;first exact:hLip.1.
  move=>x y hx hy;exact:hLip.2 x y Logic.I Logic.I.
- exact:(@coordinate_multiplicity_null_remainder_bound R n m lambda
    (u @` S) (u @` Z) c hTransportNull hTransportCount).
Qed.
