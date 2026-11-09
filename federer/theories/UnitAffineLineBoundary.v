(** Federer (1969), 3.3.19, p. 303: actual
    boundary exits along the original unit rays. General
    scalar endpoint adherence and original line continuity
    supply the boundary point; it is not selected globally. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric RealMetricBackground CoveringFamilyUP
  ScalarOpenConvexInterval UnitAffineLineGeometry UnitAffineLineSection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_affine_line_section_closure]: an
    adherent scalar section parameter maps into the
    actual closure of the original S, supporting the
    boundary choice in 3.3.19, p. 303. *)
Lemma unit_affine_line_section_closure (R:realType) n
    (z u:inner_metric_space (@euclidean_inner_productP R n))
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (t:R):
  inner_norm (@euclidean_inner_productP R n) u= 1 ->
  @closure [the topologicalType of real_line_metric R] [set r|S (z+r*:u)] t ->
  closure S (z+t*:u).
Proof.
move=>hu hClosure.
have hContinuous:=@unit_affine_line_continuous R n z u hu.
move=>V hV.
have hPreimage:nbhs (t:real_line_metric R) ((fun r:real_line_metric R=>z+r*:u) @^-1` V).
  exact:(hContinuous t V hV).
have [r [hr hVr]]:=hClosure _ hPreimage.
exists (z+r*:u);by split.
Qed.

(** Source for [unit_affine_line_upper_boundary_exit]:
    every original point of a bounded open S
    has an actual later boundary exit on each
    unit affine ray, supporting the c(B) inside S
    alternative of 3.3.19, p. 303. No
    convexity or supplied exit parameter is required
    for this supporting ray lemma. *)
Theorem unit_affine_line_upper_boundary_exit (R:realType) n
    (z u:inner_metric_space (@euclidean_inner_productP R n))
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  inner_norm (@euclidean_inner_productP R n) u= 1 ->
  open S ->metric_set_bounded S ->S (z+r*:u) ->
  exists t:R,r<t /\closure S (z+t*:u) /\~S (z+t*:u).
Proof.
move=>hu hOpen hBound hStart.
pose A:set (real_line_metric R):=[set s|S (z+s*:u)].
have hANonempty:A!=set0 by exists r.
have hAOpen:=@unit_affine_line_section_open R n z u S hu hOpen.
have hABound:=@unit_affine_line_section_bounded R n z u S hu hBound.
have [_ hLater]:=@scalar_open_member_strict_bounds R A r hAOpen hABound hStart.
have [_ hAdherent]:=@scalar_bounded_endpoints_closure R A hANonempty hABound.
exists (sup A);split=>//;split.
- exact:(@unit_affine_line_section_closure R n z u S (sup A) hu hAdherent).
- move=>hIn.
  have [_ hFalse]:=@scalar_open_member_strict_bounds R A (sup A) hAOpen hABound hIn.
  by rewrite ltxx in hFalse.
Qed.
