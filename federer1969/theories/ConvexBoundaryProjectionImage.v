(** Federer (1969), 3.2.35, p. 272:
    the projection of the original boundary
    is the projected body together with its
    boundary, or equivalently its closure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionOpenImage EuclideanProjectionBoundedClosure
  ProjectionLineNormalUP ProjectionLineNormalExistence ProjectionLineFibre ProjectionLineBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_boundary_projection_closure]:
    p(Bdry S)=closure(p(S)), underlying the
    displayed projected boundary identity in Federer
    3.2.35, p. 272. The actual two
    line endpoints lift interior projection points;
    compact source closure lifts the remaining
    points, whose lifts are outside S. No
    selected endpoint or measurable fibre premise
    is imposed on the original body. *)
Theorem convex_boundary_projection_closure (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k)
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  open S ->is_inner_convex S ->metric_set_bounded S ->
  euclidean_projection_linear p @` (closure S `\` interior S)=
    @closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R k)]
      (euclidean_projection_linear p @` S).
Proof.
move=>hOpen hConvex hBound.
have hClosure:=@euclidean_projection_bounded_closure R k.+1 k p S hBound.
apply/seteqP; split=>y.
- move=>[x [hx _] <-]; rewrite -hClosure; by exists x.
- move=>hy; case:(pselect ((euclidean_projection_linear p @` S) y))=>[[a ha <-]|hOutside].
  + have [w hW]:=@projection_line_normal_exists R k p.
    pose A:=[set t|S (a+t*:w)].
    exists (a+inf A*:w).
    * apply:(@projection_line_boundary_parameters R k p w a S hW ha hOpen hConvex hBound (inf A)).2.
      by left.
    * apply:(@projection_line_fibre R k p w a _ hW).2; by exists (inf A).
  + rewrite -hClosure in hy; have [x hx hxy]:=hy.
    exists x=>//; split; first exact hx.
    move=>hInterior; apply:hOutside; exists x=>//; exact:interior_subset hInterior.
Qed.

(** Source for [convex_boundary_projection_image]:
    the literal p(Bdry S)=p(S) union Bdry p(S)
    display in Federer 3.2.35, p. 272.
    Closure is always the union of a set
    with its closure-minus-interior boundary. *)
Theorem convex_boundary_projection_image (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k)
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  open S ->is_inner_convex S ->metric_set_bounded S ->
  let Y:=[the topologicalType of inner_metric_space (@euclidean_inner_productP R k)] in
  let P:=euclidean_projection_linear p @` S in
  euclidean_projection_linear p @` (closure S `\` interior S)= P `|` (@closure Y P `\` @interior Y P).
Proof.
move=>hOpen hConvex hBound Y P.
rewrite (@convex_boundary_projection_closure R k p S hOpen hConvex hBound).
apply/seteqP; split=>y.
- move=>hy; case:(pselect (P y))=>hP; first by left.
  right; split=>// hInterior; apply:hP; exact:interior_subset hInterior.
- move=>[hy|[hy _]]; last exact hy.
  exact:(@subset_closure Y P y hy).
Qed.
