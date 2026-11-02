(** Federer (1969), 2.10.47, pp. 204–205: the main construction after the
    reduction to null hyperplane sections. For a compact set in the root
    cube, choose a positive dyadic content, invoke the sealed pruning
    sequence, and take its intersection. This theorem retains the
    section-nullity hypothesis; the dimension-reduction argument is
    separate. Source context: DyadicPruningUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicPruningUP DyadicPruning DyadicPruningIntersection
  DyadicContentLimitBound RefiningCoverContent MetricRealPowerCost MetricRealPowerMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_null_sections_compact_subset]: the
    complete compact pruning argument of 2.10.47,
    pp. 204–205, under nullity of coordinate sections.
    The covering contents and the retained sequence are
    supplied by opaque proved witnesses. The original
    theorem does not have the section-nullity hypothesis;
    it discharges it by induction on ambient dimension. *)
Theorem dyadic_null_sections_compact_subset (R : realType) n (a : R_n R n) c p
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_metric_real_power_measure c p mu -> (0<n)%N -> (0<c)%R -> (0<p)%R -> compact A ->
  (forall x, A x -> forall l, (a l<=x l<=a l+1)%R) ->
  (forall (l : 'I_n) (t : R), mu (A `&` [set x | x l=t])=0) -> 0<mu A ->
  exists B, [/\ compact B, B `<=` A, 0<mu B & mu B< +oo].
Proof.
move=> hmu hn hc hp hA hroot hlevels hpos.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Q := @dyadic_cube_grid R n a.
have hQ : is_dyadic_cube_grid a Q := dyadic_cube_grid_specification a.
pose gamma i := @refining_cover_content R X (dyadic_cube_level Q) (metric_real_diameter_cost c p) i.
have hg i : is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i (gamma i) :=
  refining_cover_content_specification _ _ i.
have hex : exists h, 0<gamma h A.
  apply: contrapT=> hno.
  have hz j : gamma (0+j)%N A<=0.
    rewrite leNgt; apply/negP=> hj; apply: hno; by exists (0+j)%N.
  have hbound := @dyadic_contents_bound_power_measure R n a Q c p gamma mu 0%N A 0
    hQ hg hmu (ltW hc) hz.
  have hbad := lt_le_trans hpos hbound; by rewrite ltxx in hbad.
have [h hh] := hex.
pose E := @dyadic_compact_pruning R n a Q c p gamma mu hQ hg hmu hn hc hp A h hA hroot hlevels.
have hE := @dyadic_compact_pruning_specification R n a Q c p gamma mu hQ hg hmu hn hc hp A h hA hroot hlevels.
exact: (@dyadic_pruning_finite_positive_intersection R n a Q c p gamma mu h A E
  hQ hg hmu hn hc hp hroot hE hh).
Qed.
