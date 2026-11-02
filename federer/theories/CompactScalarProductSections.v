(** Compact scalar product sections supporting Federer (1969), 2.10.30, p.
    195. Compact sections admit open scalar supersets of nearly the same
    length; closed projection then controls all nearby sections. This
    supplies the upper semicontinuity ingredient in the printed compactness
    assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground InnerMetric InnerNormedTopology EuclideanInnerProduct MeasurePushforward ProductSections TopologicalProductMaps HausdorffBinaryProduct
  CompactProductSections LebesgueScalarMeasure EuclideanCompactOpenVolume EuclideanOneCoordinate
  EuclideanLebesgue EuclideanLebesgueDimensions MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_scalar_product_section]: supporting
    compactness of each scalar section of compact S
    in 2.10.30, p. 195. The parameter space
    is any Hausdorff space, and empty sections are allowed. *)
Lemma compact_scalar_product_section (R : realType) (P : topologicalType)
    (K : set (P*real_line_metric R)) (p : P) :
  hausdorff_space P -> compact K -> compact (product_vertical_section K p).
Proof.
move=> hP hK.
pose D := K `&` (fst @^-1` [set p]).
have hclosed : closed D.
  apply: closedI.
  - exact: compact_closed (hausdorff_binary_product hP (@metric_hausdorff R [the metricType R of real_line_metric R])) hK.
  - apply: (@preimage_closed (P*real_line_metric R)%type P fst [set p]).
    + by move=> x _; exact: first_projection_continuous.
    + exact (@accessible_closed_set1 P (hausdorff_accessible hP) p).
have hD : compact D by apply: (subclosed_compact hclosed hK)=> x [hx _].
have he : snd @` D=product_vertical_section K p.
  apply/seteqP; split=> t.
  - move=> [[q s] [hqs hq] <-]; change (q=p) in hq.
    by rewrite /product_vertical_section /= -hq.
  - move=> ht; exists (p,t)=> //; by split.
rewrite -he; exact: compact_product_second_projection hD.
Qed.

(** Source for [compact_scalar_section_open_bound]: supporting
    open approximation of a compact line section for
    2.10.30, p. 195, using the already proved
    one-dimensional Lebesgue open approximation. *)
Lemma compact_scalar_section_open_bound (R : realType) (A : set (real_line_metric R)) (b : R) :
  compact A -> (lebesgue_scalar_measure A<b%:E)%E ->
  exists U : set (real_line_metric R), open U /\ A `<=` U /\
    (lebesgue_scalar_measure U<b%:E)%E.
Proof.
move=> hA hb.
pose E := inner_metric_space (@euclidean_inner_productP R 1).
pose F := @euclidean_one_embed R.
pose G := @euclidean_one_project R.
have hFA : compact (F @` A).
  have hF : continuous (F : real_line_metric R -> E) := @euclidean_one_embed_continuous R.
  apply: (@continuous_compact [the topologicalType of real_line_metric R]
    [the topologicalType of E] F A)=> //.
  exact: continuous_subspaceT hF.
have hvol : @euclidean_lebesgue_measure R 1 (F @` A)=lebesgue_scalar_measure A.
  rewrite /euclidean_lebesgue_measure positive_euclidean_lebesgue_first /measure_pushforward.
  congr (lebesgue_scalar_measure _); apply/seteqP; split=> t.
  - move=> [s hs he]; have hh := congr1 G he; rewrite /G /F !euclidean_one_embedK in hh; by rewrite -hh.
  - move=> ht; by exists t.
have [W [hW [hFW hWb]]] := @euclidean_compact_open_volume_bound R 1 (F @` A) b hFA ltac:(by rewrite hvol).
exists (F @^-1` W); split.
- apply: open_comp hW=> t _; exact: euclidean_one_embed_continuous.
split.
- by move=> t ht; apply: hFW; exists t.
- have hv : lebesgue_scalar_measure (F @^-1` W)=@euclidean_lebesgue_measure R 1 W.
    by rewrite /euclidean_lebesgue_measure positive_euclidean_lebesgue_first /measure_pushforward.
  by rewrite hv.
Qed.

(** Source for [compact_scalar_product_section_upper]: supporting
    upper semicontinuity of compact scalar-section length
    used in 2.10.30, p. 195. The neighbourhood
    bounds all sections, including nearby empty ones. *)
Theorem compact_scalar_product_section_upper (R : realType) (P : topologicalType)
    (K : set (P*real_line_metric R)) (p : P) (b : R) :
  hausdorff_space P -> compact K ->
  (lebesgue_scalar_measure (product_vertical_section K p)<b%:E)%E ->
  exists V : set P, open V /\ V p /\ forall q, V q ->
    (lebesgue_scalar_measure (product_vertical_section K q)<b%:E)%E.
Proof.
move=> hP hK hb.
have [U [hU [hAU hUb]]] := compact_scalar_section_open_bound
  (@compact_scalar_product_section R P K p hP hK) hb.
pose D := K `&` ~` (snd @^-1` U).
have hclosed : closed D.
  apply: closedI.
  - exact: compact_closed (hausdorff_binary_product hP (@metric_hausdorff R [the metricType R of real_line_metric R])) hK.
  - apply: open_closedC; apply: open_comp hU=> x _; exact: second_projection_continuous.
have hD : compact D by apply: (subclosed_compact hclosed hK)=> x [hx _].
have hPD : closed (fst @` D) := compact_closed hP (compact_product_first_projection hD).
exists (~` (fst @` D)); split; first exact: closed_openC hPD.
split.
- move=> [[q t] [hqt ht] he]; change (q=p) in he.
  apply: ht; apply: hAU; by rewrite /product_vertical_section /= -he.
- move=> q hq; apply: le_lt_trans _ hUb.
  apply: (measure_mono (lebesgue_scalar_is_measure R))=> t ht.
  case: (pselect (U t))=> // hnt; exfalso; apply: hq.
  exists (q,t)=> //; by split.
Qed.
