(** Federer (1969), 3.2.35, p. 271:
    every nonempty bounded open convex Euclidean
    set has genuinely finitely rectifiable boundary. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerConvex ConvexTranslatedCombinations InnerTranslationNeighbourhood InnerTranslationBoundary
  EuclideanConvexBoundaryAtZero MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws
  MetricBoundedUnion MetricBoundedClosureLaws RectifiableSetUP LipschitzUP LipschitzRectifiableImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_convex_boundary_rectifiable]:
    the complete boundary rectifiability assertion
    of Federer 3.2.35, p. 271. A
    local member translates the original open
    bounded convex body to contain zero; the
    corrected radial-map proof applies there.
    Exact translated neighbourhoods preserve the
    original boundary and unit translation preserves
    genuine finite rectifiability. No centre,
    inner ball, gauge or parametrization is
    an added hypothesis. The n=1 boundary uses
    the printed finite-set degree-zero convention. *)
Theorem euclidean_open_convex_boundary_rectifiable (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->open S ->is_inner_convex S ->metric_set_bounded S ->
  is_m_rectifiable (n-1) (closure S `\` interior S).
Proof.
move=>[a ha] hOpen hConvex hBound.
pose V:=R_n R n.
pose hB:=@euclidean_inner_productP R n.
pose E:=inner_metric_space hB.
pose U:set E:=(fun x:V=>x+a) @^-1` S.
have hOpenU:open U.
  rewrite openE=>x hx.
  apply:(@inner_translation_neighbourhood R V (@euclidean_inner_product R n) hB a x S).1.
  exact:(open_nbhs_nbhs (conj hOpen hx)).
have hConvexU:is_inner_convex U.
  exact:(@convex_translate_to_origin R V S a hConvex).
have hZeroU:U 0 by change (S (0+a)); rewrite add0r.
have [r [hr hRadius]]:=@metric_bounded_distance_bound R E S a hBound.
have hSubset:U `<=` metric_closed_ball (0:E) r.
  move=>x hx; have hh:=hRadius (x+a) hx.
  have hDistance:=@inner_translation_distance R V (@euclidean_inner_product R n) hB a 0 x.
  rewrite add0r in hDistance.
  change (is_true (mdist (0:E) x<=r)); by rewrite -hDistance.
have hBoundU:metric_set_bounded U.
  exact:(metric_bounded_subset hSubset (@covering_closed_ball_bounded R E 0 r hr)).
have hRectU:=@euclidean_convex_boundary_at_zero_rectifiable R n U hOpenU hConvexU hZeroU hBoundU.
have hLip:@is_metric_lipschitz R E E (closure U `\` interior U) (fun x=>x+a).
  exists 1; split; first exact:ltr01.
  split; first exact:ler01.
  move=>x y _ _.
  by rewrite (@inner_translation_distance R V (@euclidean_inner_product R n) hB a x y) mul1r.
have hResult:=@rectifiable_lipschitz_image R E E (n-1) (closure U `\` interior U)
  (fun x=>x+a) hLip hRectU.
by rewrite (@inner_translation_boundary_image R V (@euclidean_inner_product R n) hB S a) in hResult.
Qed.
