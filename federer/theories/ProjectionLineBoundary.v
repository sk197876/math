(** Federer (1969), 3.2.35, p. 272:
    the two actual endpoints of an open convex
    projection-line section are precisely its
    intersections with the original boundary. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  RealMetricBackground RealOpenIntervals ScalarOpenConvexInterval CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectionLineNormalUP ProjectionLineFibre
  ProjectionLineSection ProjectionLineSectionClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_line_boundary_parameters]:
    the two-point boundary-fibre assertion in Federer
    3.2.35, p. 272. The actual scalar
    infimum and supremum belong to the line
    closure and are outside the original open S.
    Conversely a boundary parameter lies in their
    closed interval and cannot be in its interior.
    No endpoint or closure-section law is assumed. *)
Theorem projection_line_boundary_parameters (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w a
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  is_projection_line_normal p w ->S a ->open S ->is_inner_convex S ->metric_set_bounded S ->
  let A:set (real_line_metric R):=[set t|S (a+t*:w)] in
  forall t:R,(closure S `\` interior S) (a+t*:w) <->t=inf A \/t=sup A.
Proof.
move=>hW ha hOpen hConvex hBound A.
have [hLower [hUpper hInterval]]:=@projection_open_convex_line_interval R k p w a S hW ha hOpen hConvex hBound.
change (A=real_open_interval (inf A) (sup A)) in hInterval.
have hNonempty:A!=set0 by exists 0; change (S (a+0*:w)); rewrite scale0r addr0.
have hBoundA:=@projection_line_section_bounded R k p w a S hW hBound.
have [hInfClosure hSupClosure]:=@scalar_bounded_endpoints_closure R A hNonempty hBoundA.
have hClosure:=fun t=>@projection_line_section_closure R k p w a S t hW ha hOpen hConvex.
move=>t; split.
- move=>[hInClosure hOutside].
  have hScalarClosure:closure A t:=(hClosure t).2 hInClosure.
  rewrite hInterval in hScalarClosure.
  have [hl hu]:=real_open_interval_closure_bounds hScalarClosure.
  case:(eqVneq t (inf A))=>htl; first by left.
  case:(eqVneq t (sup A))=>htu; first by right.
  exfalso; apply:hOutside; apply:open_nbhs_nbhs; split; first exact hOpen.
  change (A t); rewrite hInterval; split; lra.
- move=>[->|->]; split.
  + exact:(hClosure (inf A)).1 hInfClosure.
  + move=>hInterior; have hh:A (inf A):=interior_subset hInterior.
    rewrite {1}hInterval in hh; have [hStrict _]:=hh; by rewrite ltxx in hStrict.
  + exact:(hClosure (sup A)).1 hSupClosure.
  + move=>hInterior; have hh:A (sup A):=interior_subset hInterior.
    rewrite {1}hInterval in hh; have [_ hStrict]:=hh; by rewrite ltxx in hStrict.
Qed.

(** Source for [projection_line_boundary_fibre]: the
    actual fibre of the original boundary is
    the pair of distinct section endpoints,
    Federer 3.2.35, p. 272. Exact
    kernel spanning supplies every original fibre
    point, before any counting integral is used. *)
Theorem projection_line_boundary_fibre (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w a
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  is_projection_line_normal p w ->S a ->open S ->is_inner_convex S ->metric_set_bounded S ->
  let A:set (real_line_metric R):=[set t|S (a+t*:w)] in
  [set x| (closure S `\` interior S) x /\euclidean_projection_linear p x=euclidean_projection_linear p a]=
    [set a+inf A*:w] `|` [set a+sup A*:w].
Proof.
move=>hW ha hOpen hConvex hBound A.
have hBoundary:=@projection_line_boundary_parameters R k p w a S hW ha hOpen hConvex hBound.
apply/seteqP; split=>x.
- move=>[hx hp].
  have [t hxt]:=(@projection_line_fibre R k p w a x hW).1 hp.
  rewrite hxt in hx *.
  have [->|->]:=(hBoundary t).1 hx; [by left|by right].
- move=>[->|->]; split.
  + apply:(hBoundary (inf A)).2; by left.
  + apply:(@projection_line_fibre R k p w a _ hW).2; by exists (inf A).
  + apply:(hBoundary (sup A)).2; by right.
  + apply:(@projection_line_fibre R k p w a _ hW).2; by exists (sup A).
Qed.
