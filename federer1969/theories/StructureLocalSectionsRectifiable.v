(** Federer (1969), 3.3.5, p. 292: countable rectifiability
    follows from actual global sections on all small original subsets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace StructureGraphSectionUP MetricClosedSmallCover
  EuclideanMetricSeparability MetricDiameterUP MetricDiameter StructureConeDensityValues
  RectifiableSetUP RectifiableElementary CountablyRectifiableUnions
  EuclideanLipschitzRectifiableImage LipschitzBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_small_sections_countably_rectifiable]: the
    final conclusion of Federer 3.3.5, p. 292. A countable small-diameter
    Euclidean cover gives original subsets, each contained in a genuine
    global Lipschitz section image. The established image and subset
    laws of 3.2.14 give an exact countable rectifiable cover, including
    degree zero and empty or nonmeasurable original sets. *)
Theorem structure_small_sections_countably_rectifiable (R:realType) n m
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (r: \bar R) (s:R):
  (0<r)%E ->(forall S,S `<=` E ->(extended_metric_diameter S<r)%E ->
    exists f,is_structure_projection_section S p s f) ->is_countably_m_rectifiable m E.
Proof.
move=>hr hSections.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [q [hQ0 hQR]]:=extended_rationals_order_dense hr.
pose t:=(ratr q:R).
have ht:0<t by move:hQ0; rewrite lte_fin.
have hHalf:=structure_density_positive_half_bounds ht.
have [D [hD hDense]]:=@euclidean_metric_separable R n.
have [F [hF hCover]]:=@separable_closed_small_cover_allow_empty R X D setT (t/2)
  hD hDense closedT (andP hHalf).1.
pose S i:=E `&` F i.
have hUnion:E=\bigcup_i S i.
  apply/seteqP; split=>x.
  - move=>hx; have hWhole:(\bigcup_i F i) x by rewrite -hCover.
    have [i _ hi]:=hWhole; exists i=>//; by split.
  - by move=>[i _ [hx _]].
rewrite hUnion; apply:countably_rectifiable_countable_union (countableP setT) _=>i _.
have hSubset:S i `<=` E by move=>x [hx _].
have hBound:(extended_metric_diameter (S i)<=(t/2)%:E)%E.
  apply:(metric_diameter_least (extended_metric_diameter_specification (S i))).
  - by rewrite lee_fin; exact:ltW (andP hHalf).1.
  - move=>x y [_ hx] [_ hy]; rewrite lee_fin; exact:(hF i).2.2 x y hx hy.
have hDiameter:(extended_metric_diameter (S i)<r)%E.
  have hSmall:((t/2)%:E<t%:E)%E by rewrite lte_fin; exact:(andP hHalf).2.
  exact:le_lt_trans hBound (lt_trans hSmall hQR).
have [f [hLip [hSection hImage]]]:=hSections (S i) hSubset hDiameter.
apply:countably_rectifiable_subset hImage _.
exact:euclidean_lipschitz_image_countably_rectifiable (metric_lipschitz_of_bound hLip).
Qed.
