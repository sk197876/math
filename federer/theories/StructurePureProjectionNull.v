(** Federer (1969), 3.3.12, p. 297: the actual fixed-projection
    nullity argument after the original 3.3.10 structure conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions StructureConeUP StructureProjectionKernel StructureIncidenceSets
  StructureFixedProjectionAssertions StructureProjectionConditions
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_pure_projection_null]: supporting all three
    null projected pieces in the proof of Federer 3.3.12, p. 297.
    The original 3.3.10 final assertion is used at the fixed projection;
    condition (I) makes its null original source piece project to zero,
    condition (II) makes the original S3 section project to zero, and
    actual 3.3.10 gives the S2 section for every original projection.
    The original pure source A is retained without an image hull. *)
Theorem structure_pure_projection_null (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->phi A< +oo ->A `<=` E ->
  structure_projection_preserves_null_subsets phi E p ->
  structure_projection_almost_finite_fibres E p ->
  phi (A `&` [set a|~(@structure_second_incidence R n m phi A `|`
    @structure_third_incidence R n m A) (a,structure_projection_kernel hmn p)])=0 ->
  euclidean_lebesgue_measure m (euclidean_projection_linear p @` A)=0.
Proof.
move=>hStructure hFinite hAE hI hII hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose f:=euclidean_projection_linear p.
pose S2:=@structure_second_incidence R n m phi A.
pose S3:=@structure_third_incidence R n m A.
pose B2:set X:=[set a|S2 (a,structure_projection_kernel hmn p)].
pose B3:set X:=[set a|S3 (a,structure_projection_kernel hmn p)].
pose U:=A `&` [set a|~(S2 `|` S3) (a,structure_projection_kernel hmn p)].
pose L:=@euclidean_lebesgue_measure R m.
have hL:is_measure L:=euclidean_lebesgue_is_measure R m.
have hNullU:L (f @` U)=0.
  apply: (hI U _ hNull); by move=>x [hx _]; exact:hAE hx.
have hNull2:L (f @` B2)=0.
  exact:(@structure_second_projection_section_null R n m hmn phi A p hStructure hFinite).
have hNull3:L (f @` B3)=0.
  apply:(@measure_null_subset R [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    L hL (f @` B3)
    (~` [set y|finite_set (E `&` f @^-1` [set y])]) _ hII).
  move=>y hy hFibre.
  have hInfinite:=@structure_third_projection_section_infinite R n m hmn A p y hy.
  apply:hInfinite.
  apply: (sub_finite_set _ hFibre).
  by move=>x [hx hfx]; split; first exact:hAE hx.
have hUnionNull:=measure_null_union hL hNullU (measure_null_union hL hNull2 hNull3).
apply:(@measure_null_subset R [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  L hL (f @` A) ((f @` U) `|` ((f @` B2) `|` (f @` B3))) _ hUnionNull).
move=>y [x hx <-].
case:(pselect (B2 x))=>h2.
- right; left; by exists x.
- case:(pselect (B3 x))=>h3.
  + right; right; by exists x.
  + left; exists x; last by [].
    split; first exact:hx.
    by move=>[hh|hh]; [exact:h2 hh|exact:h3 hh].
Qed.
