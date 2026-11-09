(** Federer (1969), 3.3.19, p. 303: actual
    original boundary points xi(B) in f^{-1}(B) intersect
    Bdry S, with f(xi(B))=c(B) when c(B) is in S.
    Construct the radial map and both kinds of boundary
    point; no auxiliary map or point is a theorem premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  MetricClosedBalls CoveringFamilyUP LipschitzUP CircularTrigonometrySealed CircularUnitVectors
  CircularDiscRefinement CircularDiscCentreRadius RadialBallRetractionUP EuclideanRadialBallRetraction
  UnitAffineLineBoundary ConvexBallBoundaryPoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Selection.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_disc_boundary_selection_exists]:
    complete actual boundary-point choice of 3.3.19,
    p. 303. For each original child B meeting
    the original bounded open convex S, xi is on
    Bdry S and f(xi) is in B. If its centre
    is in S, the actual outward-ray exit retracts
    exactly to that centre. The outside-centre case
    uses an actual boundary point in B and
    nonexpansion with its fixed centre. All auxiliaries
    remain existential and local. *)
Theorem circular_disc_boundary_selection_exists (z:E) (r:R) n (S:set E):
  0<r ->(4<=n)%N ->open S ->is_inner_convex S ->metric_set_bounded S ->
  exists P:E->E,@is_radial_ball_retraction R (R_n R 2) (@euclidean_inner_product R 2) hE z (r-r/n%:R) P /\
  forall k:'I_n,metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) `&` S!=set0 ->
    exists xi:E,(closure S `\` interior S) xi /\
      metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) (P xi) /\
      (S (circular_disc_child_center z r k) ->P xi=circular_disc_child_center z r k).
Proof.
move=>hr hn hOpen hConvex hBound.
have hnP:(0<n)%N:=leq_trans (erefl true : (1<=4)%N) hn.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hSmaller:r/n%:R<r by rewrite ltr_pdivrMr //;nra.
have hInner:0<=r-r/n%:R by lra.
have hChild:0<r/n%:R by rewrite divr_gt0.
have [P hP]:=@euclidean_radial_ball_retraction_exists R 2 z (r-r/n%:R) hInner.
exists P;split=>//;move=>k hMeet.
pose c:E:=circular_disc_child_center z r k.
case:(pselect (S c))=>hCentre.
- pose u:E:=circular_unit_vector (2* p* k%:R/n%:R).
  have hu:inner_norm hE u= 1 by exact:circular_unit_vector_norm.
  have hPosition:c=z+(r-r/n%:R)*:u.
    rewrite /c /circular_disc_child_center -/u;congr (z+_*:u);ring.
  have hStart:S (z+(r-r/n%:R)*:u) by rewrite -hPosition.
  have [d [hLater [hClosure hOutside]]]:=@unit_affine_line_upper_boundary_exit R 2 z u S
    (r-r/n%:R) hu hOpen hBound hStart.
  pose xi:E:=z+d*:u.
  have hRetracted:P xi=c.
    rewrite /xi (@radial_ball_retraction_ray R (R_n R 2) (@euclidean_inner_product R 2) hE
      z (r-r/n%:R) P hP u d hu (ltW hLater)).
    exact:esym hPosition.
  exists xi;split.
  + split;first exact hClosure.
    move=>hInterior;apply:hOutside;exact:interior_subset hInterior.
  + split.
    * rewrite hRetracted;change (is_true (mdist c c<=r/n%:R));rewrite mdistxx;exact:ltW hChild.
    * by move=>_.
- have [xi [hxBall hxBoundary]]:=@convex_ball_boundary_point_exists R 2 S c (r/n%:R)
    hOpen hConvex hBound hCentre hMeet.
  have hcBall:metric_closed_ball z (r-r/n%:R) c.
    change (is_true (mdist z c<=r-r/n%:R)).
    by rewrite /c (@circular_disc_child_centre_radius R z r n k (ltW hr) hnP).
  have hFixed:=@radial_ball_retraction_fixed R (R_n R 2) (@euclidean_inner_product R 2) hE
    z (r-r/n%:R) P hP c hcBall.
  have hContraction:=(@radial_ball_retraction_nonexpanding R (R_n R 2) (@euclidean_inner_product R 2) hE
    z (r-r/n%:R) P hP).2 c xi Logic.I Logic.I.
  rewrite hFixed mul1r in hContraction.
  exists xi;split=>//;split.
  + exact:le_trans hContraction hxBall.
  + move=>hInside;exfalso;exact:hCentre hInside.
Qed.
End Selection.
