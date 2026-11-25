(** Federer (1969), 3.2.35, p. 272:
    actual orthogonal projection commutes with closure
    of a bounded Euclidean source. The compact
    source closure supplies the reverse inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric MetricBoundedClosureLaws CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_projection_bounded_closure]:
    supporting p(Bdry S)=p(S) union Bdry p(S)
    in Federer 3.2.35, p. 272. Continuity
    gives the forward closure inclusion; the
    image of the proved compact source closure
    is closed and contains p(S), giving the
    reverse. The supporting theorem needs no
    convexity, openness or source measurability. *)
Theorem euclidean_projection_bounded_closure (R:realType) n m
    (p:orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  metric_set_bounded S ->
  euclidean_projection_linear p @` closure S=
    @closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
      (euclidean_projection_linear p @` S).
Proof.
move=>hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose F:X->Y:=euclidean_projection_linear p.
have hF:continuous F:=@euclidean_projection_continuous R n m p.
have hCompact:@compact [the topologicalType of X] (closure S).
  exact:euclidean_bounded_closure_compact hBound.
have hImageCompact:@compact [the topologicalType of Y] (F @` closure S).
  exact:continuous_compact (continuous_subspaceT hF) hCompact.
have hImageClosed:@closed [the topologicalType of Y] (F @` closure S).
  exact:compact_closed (@metric_hausdorff R Y) hImageCompact.
have hPreClosed:@closed [the topologicalType of X]
    (F @^-1` (@closure [the topologicalType of Y] (F @` S))).
  exact:((@continuous_closedP [the topologicalType of X] [the topologicalType of Y] F).1
    hF _ (@closed_closure [the topologicalType of Y] (F @` S))).
have hPreSubset:S `<=` F @^-1` (@closure [the topologicalType of Y] (F @` S)).
  move=>x hx; apply:(@subset_closure [the topologicalType of Y] (F @` S)).
  by exists x.
have hImageSubset:F @` S `<=` F @` (@closure [the topologicalType of X] S).
  move=>y [x hx <-]; exists x; last reflexivity.
  exact:(@subset_closure [the topologicalType of X] S x hx).
apply/seteqP; split=>y.
- move=>[x hx <-].
  exact:(hPreClosed x (@closureS [the topologicalType of X] S _ hPreSubset x hx)).
- move=>hy.
  exact:(hImageClosed y (@closureS [the topologicalType of Y]
    (F @` S) (F @` closure S) hImageSubset y hy)).
Qed.
