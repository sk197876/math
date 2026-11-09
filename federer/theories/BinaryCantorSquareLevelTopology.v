(** Federer (1969), 3.3.20, p. 307: the actual nested compact square levels and their original limit. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology cardinality.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  SpecialIntervalTreeTopology EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct EuclideanIntervalRectangles CantorSquareCompactMass
  BinaryCantorSquareLevelsUP BinaryCantorSquareCover CompactCellRecombination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [original_interval_rectangle_compact]: supporting compactness
    of the actual original square generators of 3.3.20, p. 307. *)
Lemma original_interval_rectangle_compact (R:realType) (S T:compact_real_intervals R):
  compact (euclidean_interval_rectangle S T).
Proof.
exact:(@euclidean_cantor_product_compact R (val S) (val T)
  (compact_real_interval_compact (set_valP S)) (compact_real_interval_compact (set_valP T))).
Qed.

(** Source for [original_square_level_union_compact]: the actual finite
    level union in the projection argument of 3.3.20, p. 307, is compact. *)
Lemma original_square_level_union_compact (R:realType)
    (F:{fset (compact_real_intervals R*compact_real_intervals R)}):
  compact (\bigcup_(P in [set` F]) euclidean_interval_rectangle P.1 P.2).
Proof.
apply:compact_finite_indexed_union;first exact:finite_fset.
move=>P _;exact:original_interval_rectangle_compact.
Qed.

(** Source for [original_square_level_union_closed]: the actual finite
    square-level unions of 3.3.20, p. 307, are closed in the actual plane. *)
Lemma original_square_level_union_closed (R:realType)
    (F:{fset (compact_real_intervals R*compact_real_intervals R)}):
  closed (\bigcup_(P in [set` F]) euclidean_interval_rectangle P.1 P.2).
Proof.
exact:(compact_closed (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)])
  (@original_square_level_union_compact R F)).
Qed.

(** Source for [binary_original_square_level_union_decreasing]: the
    original G_j unions decrease in 3.3.20, p. 307. Actual factor
    ancestor containment proves this for every pair of levels. *)
Lemma binary_original_square_level_union_decreasing (R:realType) (h:R->R) H G:
  is_special_interval_tree h H ->is_binary_cantor_square_levels H G ->
  forall n m,(n<=m)%N ->
    (\bigcup_(P in [set` G m]) euclidean_interval_rectangle P.1 P.2) `<=`
    (\bigcup_(P in [set` G n]) euclidean_interval_rectangle P.1 P.2).
Proof.
move=>hTree hG n m hnm x [P hP [hx0 hx1]].
have hPM:=hP;change (is_true (P \in G m)) in hPM;rewrite hG in_fsetM in hPM;move:hPM=>/andP[hS hT].
have hxFirst:(\bigcup_(S in [set` H m]) val S) (euclidean_real_plane_first x) by exists P.1.
have hxSecond:(\bigcup_(T in [set` H m]) val T) (euclidean_real_plane_second x) by exists P.2.
have [S hS0 hxS]:=@special_interval_level_union_antitone R h H hTree n m hnm _ hxFirst.
have [T hT0 hxT]:=@special_interval_level_union_antitone R h H hTree n m hnm _ hxSecond.
exists (S,T);first by change (is_true ((S,T) \in G n));rewrite hG in_fsetM hS0 hT0.
by split.
Qed.

(** Source for [binary_original_square_limit_identity]: E is the
    intersection of the actual original square-level unions in 3.3.20,
    p. 307. This is proved from the original factor limit laws. *)
Lemma binary_original_square_limit_identity (R:realType) H G (A:set (real_line_metric R)):
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  euclidean_cantor_product A A=
    \bigcap_j (\bigcup_(P in [set` G j]) euclidean_interval_rectangle P.1 P.2).
Proof.
move=>hA hG;apply/seteqP;split=>x.
- move=>hx j _;have [P [hP hxP]]:=binary_cantor_original_square_level_cover hA hG j hx.
  by exists P.
- move=>hx;split;apply/(hA _);move=>j;
    have [P hP [hx0 hx1]]:=hx j Logic.I;
    have hPM:=hP;change (is_true (P \in G j)) in hPM;rewrite hG in_fsetM in hPM;move:hPM=>/andP[hS hT].
  + exists P.1;by split.
  + exists P.2;by split.
Qed.
