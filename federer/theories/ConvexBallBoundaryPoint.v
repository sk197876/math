(** Federer (1969), 3.3.19, p. 303: when
    the original disc centre is outside the bounded open
    convex S and its disc meets S, an actual point
    of that disc lies on the actual boundary of S.
    No boundary point is assumed or globally selected. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormalization InnerMetric
  InnerConvex MetricClosedBalls RealMetricBackground CoveringFamilyUP ScalarOpenConvexInterval
  UnitAffineLineGeometry UnitAffineLineSection UnitAffineLineBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_ball_boundary_point_exists]: actual
    boundary point for the c(B) outside S case
    in 3.3.19, p. 303. A unit line
    through an actual meeting point has an original
    interval section. Its lower endpoint lies between
    the original centre and that meeting point, remains
    in the original disc and lies on Bdry S. *)
Theorem convex_ball_boundary_point_exists (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (c:inner_metric_space (@euclidean_inner_productP R n)) (r:R):
  open S ->is_inner_convex S ->metric_set_bounded S ->~S c ->
  metric_closed_ball c r `&` S!=set0 ->
  exists xi:inner_metric_space (@euclidean_inner_productP R n),
    metric_closed_ball c r xi /\(closure S `\` interior S) xi.
Proof.
move=>hOpen hConvex hBound hc [x [hxBall hxS]].
pose hE:=@euclidean_inner_productP R n.
have hNonzero:x-c!= 0.
  apply/negP=>/eqP hZero;have hEqual:x=c by apply/eqP;by rewrite -subr_eq0 hZero eqxx.
  apply:hc;by rewrite -hEqual.
pose d:R:=inner_norm hE (x-c).
pose u:inner_metric_space hE:=inner_normalize hE (x-c).
have hu:inner_norm hE u= 1:=inner_normalize_norm hE hNonzero.
have hd:0<d by rewrite /d inner_norm_gt0.
have hPoint:c+d*:u=x by rewrite /d /u inner_normalizeK // addrC subrK.
pose A:set (real_line_metric R):=[set t|S (c+t*:u)].
have hAd:A d by rewrite /A /= hPoint.
have hANonempty:A!=set0 by exists d.
have hAOpen:=@unit_affine_line_section_open R n c u S hu hOpen.
have hAConvex:=@unit_affine_line_section_convex R n c u S hConvex.
have hABound:=@unit_affine_line_section_bounded R n c u S hu hBound.
have [hLeft hRight]:=@scalar_open_member_strict_bounds R A d hAOpen hABound hAd.
have [_ hInterval]:=@scalar_open_convex_interval R A hANonempty hAOpen hAConvex hABound.
have hLower:0<=inf A.
  case:(leP 0 (inf A))=>[h|h];first by [].
  have hZero:A 0 by rewrite hInterval;split;lra.
  apply:False_ind;apply:hc;by move:hZero;rewrite /A /= scale0r addr0.
have [hAdherent _]:=@scalar_bounded_endpoints_closure R A hANonempty hABound.
pose xi:inner_metric_space hE:=c+(inf A)*:u.
have hClosure:closure S xi:=@unit_affine_line_section_closure R n c u S (inf A) hu hAdherent.
have hOutside:~S xi.
  move=>hIn.
  have [hFalse _]:=@scalar_open_member_strict_bounds R A (inf A) hAOpen hABound hIn.
  by rewrite ltxx in hFalse.
have hOuter:mdist c x=d by rewrite inner_metric_distanceE -[c-x]opprB inner_normN.
have hRadius:d<=r by rewrite -hOuter;exact hxBall.
have hDistance:mdist c xi=inf A.
  have hh:=@unit_affine_line_distance R n c u 0 (inf A) hu.
  by rewrite scale0r addr0 sub0r normrN (ger0_norm hLower) in hh.
exists xi;split.
- change (is_true (mdist c xi<=r));rewrite hDistance;exact:le_trans (ltW hLeft) hRadius.
- split=>//;move=>hInterior;apply:hOutside;exact:interior_subset hInterior.
Qed.
