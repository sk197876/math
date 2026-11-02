(** Federer (1969), 3.2.35, p. 272:
    closure on an actual projection line through
    an interior source member agrees with the
    original source closure on that line. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground RealNormUP
  InnerConvex OpenConvexContractions NormSmallStrictContraction EuclideanProjectionSpace EuclideanProjectionMetric
  ProjectionLineNormalUP ProjectionLineSection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_line_section_closure]: supporting
    the exact two endpoints of an interior
    projected boundary fibre in Federer 3.2.35,
    p. 272. Continuity proves one direction.
    For the converse, strict contraction of a
    closure point toward the original member a
    remains in the original open convex S;
    its scalar parameters approach the original t.
    The original-member premise is retained, since
    a merely tangent line need not meet S. *)
Theorem projection_line_section_closure (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w a
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) t:
  is_projection_line_normal p w ->S a ->open S ->is_inner_convex S ->
  let A:set (real_line_metric R):=[set s|S (a+s*:w)] in
  @closure [the topologicalType of real_line_metric R] A t <->
    closure S (a+t*:w).
Proof.
move=>hW ha hOpen hConvex A.
pose E:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose F:real_line_metric R->E:=fun s=>a+s*:w.
have hF:continuous F:=@projection_line_continuous R k p w a hW.
split.
- move=>ht.
  have hPreClosed:@closed [the topologicalType of real_line_metric R] (F @^-1` closure S).
    exact:((@continuous_closedP [the topologicalType of real_line_metric R]
      [the topologicalType of E] F).1 hF _ (@closed_closure [the topologicalType of E] S)).
  have hSubset:A `<=` F @^-1` closure S.
    move=>s hs; exact:(@subset_closure [the topologicalType of E] S (F s) hs).
  exact:(hPreClosed t (@closureS [the topologicalType of real_line_metric R]
    A _ hSubset t ht)).
- move=>ht U hU.
  have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
    (t:real_line_metric R) U) hU.
  have [s [hs0 [hs1 hNear]]]:=@norm_small_strict_contraction R R^o
    (fun v:R^o=>`|v|) (@scalar_absolute_value_norm R) t d hd.
  have hInside:=@open_convex_contraction_closure R (R_n R k.+1)
    (@euclidean_inner_product R k.+1) (@euclidean_inner_productP R k.+1)
    S a (a+t*:w) s hOpen hConvex ha ht hs0 hs1.
  rewrite scalerDr addrA -scalerDl subrK scale1r scalerA in hInside.
  exists (s*t); split; first exact hInside.
  apply:hBall; change (is_true (`|t-s*t|<d)).
  change (is_true (`|s*t-t|<d)) in hNear.
  by rewrite distrC.
Qed.
