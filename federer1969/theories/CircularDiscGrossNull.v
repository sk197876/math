(** Federer (1969), 3.3.19, p. 306: the original
    compact circular-disc set has zero Gross measure,
    although its Hausdorff and convex projection masses are positive. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric CoordinateProjection
  EuclideanProjectionSpace EuclideanLebesgueDimensions CompactProjectionFamilyUP
  GrossCompactProjectionSupremum ProjectionMeasure MeasureUP MeasureBasic
  CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscRadialMapUP PartialFunctionUP
  CircularDiscProjectionNull TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Gross.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.
Variable eta:nat->partial_function E E.
Hypothesis hEta:forall j,is_circular_disc_radial_map H j (eta j).

(** Source for [circular_disc_linear_projection_null]: the
    same every-p zero-length assertion of 3.3.19, p. 306
    with the printed linear O*(2,1) presentation. Actual
    projection-space completeness proves equivalence of presentations. *)
Lemma circular_disc_linear_projection_null (p:{linear R_n R 2->R_n R 1}):
  O_star p ->euclidean_lebesgue_measure 1 (p @` A)= 0%E.
Proof.
move=>hp.
have [q hQ]:= @euclidean_projection_linear_complete R 2 1 p hp.
have hEqual:(euclidean_projection_linear q @` A)=(p @` A).
  apply/seteqP;split=>y [x hx <-];exists x=>//;by rewrite hQ.
have hNull:= @circular_disc_every_projection_null R H hH A hA eta hEta q.
by rewrite hEqual in hNull.
Qed.

(** Source for [circular_disc_gross_measure_zero]: the
    final Gross-null assertion in the first paragraph of
    3.3.19, p. 306. Every original compact projected
    subfamily has zero cost, because EVERY original
    projection is null. The proved Borel compact-family
    characterization identifies the actual Gross measure;
    no measurable source replacement is introduced. *)
Theorem circular_disc_gross_measure_zero:@gross_measure R 2 1 A= 0%E.
Proof.
have [_ hCompact]:= @circular_disc_limit_nonempty_compact R H hH A hA.
have hBorel:borel_set A:= closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of E]) hCompact).
have hMeasure:= @gross_measure_is_measure R 2 1 (leqnSn 1).
apply/eqP;rewrite eq_le (measure_nonnegative hMeasure) andbT.
apply:(@gross_borel_compact_projection_least_bound R 2 1 A 0 (leqnSn 1) hBorel).
move=>v [I [K [p [hFamily ->]]]].
have hEach i:euclidean_lebesgue_measure 1 (p i @` K i)= 0%E.
  have hAll:= circular_disc_linear_projection_null (compact_projected_family_projection hFamily i).
  have hSubset:(p i @` K i) `<=` (p i @` A).
    move=>y [x hx <-].
    have hxA:A x:=compact_projected_family_subset hFamily hx.
    by exists x.
  exact:(@MeasureAlmostBasic.measure_null_subset R _ (@euclidean_lebesgue_measure R 1)
    (@euclidean_lebesgue_is_measure R 1) _ _ hSubset hAll).
by rewrite (eq_bigr (fun _=>0%E)) // big1.
Qed.
End Gross.
