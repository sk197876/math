(** Federer (1969), 3.2.35, p. 271:
    finite rectifiability of the actual bounded open
    convex boundary after translation to contain zero.
    Use the erratum-corrected sphere map and proved bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormMetric InnerConvex InnerOwnNormDiameter InnerOwnNormBoundary CoveringFamilyUP
  NormConvexRadialBoundaryImage NormConvexRadialBoundaryLipschitz RadialGaugeMapUP
  EuclideanUnitSphereRectifiable PartialFunctionUP PartialMetricLipschitz
  RectifiableSetUP LipschitzUP LipschitzBasic LipschitzRectifiableImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_convex_boundary_at_zero_rectifiable]:
    the first boundary rectifiability assertion in
    Federer 3.2.35, p. 271, under the
    printed auxiliary assumption zero in S. The
    corrected actual sphere map, erratum p. 5,
    book p. 271 line 24, has proved exact
    boundary image and Lipschitz bound. Genuine
    finite sphere rectifiability transfers to the
    original boundary in its actual Euclidean metric.
    All natural ambient dimensions are retained,
    using the degree-zero finite-set convention. *)
Theorem euclidean_convex_boundary_at_zero_rectifiable (R:realType) n
    (S:set (R_n R n)):
  @open [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] S ->
  is_inner_convex S ->S 0 ->
  @metric_set_bounded R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] S ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
    (@closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] S `\`
      @interior [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] S).
Proof.
move=>hOpen hConvex hZero hBound.
pose V:=R_n R n.
pose hB:=@euclidean_inner_productP R n.
pose N:=inner_norm hB.
pose hN:=inner_norm_real_norm hB.
pose E:=inner_metric_space hB.
pose Sphere:set E:=[set x|N x= 1].
have hOpenN:=(@inner_own_norm_open_iff R V (@euclidean_inner_product R n) hB S).1 hOpen.
have hBoundN:=(@inner_own_norm_bounded_iff R V (@euclidean_inner_product R n) hB S).1 hBound.
have [g [f [hG [hF hImage]]]]:=@norm_convex_radial_boundary_map_exists R V N hN S
  hOpenN hConvex hZero hBoundN.
have [L hL]:=@norm_convex_radial_boundary_lipschitz R V N hN S g f
  hG hOpenN hConvex hZero hBoundN hF.
pose F:E->E:=fun x=>(g x)^-1*:x.
have hGraph x (hx:Sphere x):partial_function_graph f x (F x).
  apply:(@radial_gauge_map_graph_law R V N g f hF x (F x)).2.
  by split.
have hLip:@is_metric_lipschitz R E E Sphere F.
  apply:(@metric_lipschitz_of_bound R E E Sphere F L); split; first exact hL.1.
  move=>x y hx hy.
  have hh:=hL.2 x y (F x) (F y) (hGraph x hx) (hGraph y hy).
  change (is_true (N (F x-F y)<=L*N (x-y))) in hh.
  exact hh.
have hRange:F @` Sphere=partial_function_range f.
  apply/seteqP; split=>y.
  - move=>[x hx <-]; exists x; exact:hGraph x hx.
  - move=>[x hx]; have [hUnit hValue]:=(@radial_gauge_map_graph_law R V N g f hF x y).1 hx.
    exists x; first exact hUnit.
    exact hValue.
have hRect:=@rectifiable_lipschitz_image R E E (n-1) Sphere F hLip
  (@euclidean_unit_sphere_rectifiable R n).
rewrite hRange hImage in hRect.
by rewrite -(@inner_own_norm_boundary R V (@euclidean_inner_product R n) hB S) in hRect.
Qed.
