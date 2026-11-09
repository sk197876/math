(** Federer (1969), 3.3.19, p. 304:
    an actual simple closed curve parametrizes the
    original bounded open convex boundary. Translation
    removes the auxiliary zero-in-body condition. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  InnerConvex ConvexTranslatedCombinations InnerTranslationNeighbourhood InnerTranslationBoundary
  InnerOwnNormDiameter InnerOwnNormBoundary MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws
  MetricBoundedUnion MetricBoundedClosureLaws NormMetric ConvexRadialCircularCurve CircularTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_boundary_circular_curve_exists]:
    the original convex boundary needed in the
    cyclic-point sum of 3.3.19, p. 304.
    Original nonemptiness supplies a local translation;
    the corrected radial map and actual circle prove
    the full boundary image and simple closed curve
    laws. No auxiliary centre, curve or regularity
    is added as a hypothesis. *)
Theorem convex_boundary_circular_curve_exists (R:realType)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))):
  S!=set0 ->open S ->is_inner_convex S ->metric_set_bounded S ->
  exists (C:R->inner_metric_space (@euclidean_inner_productP R 2)) (L:R),
    0<=L /\(forall a b,mdist (C a) (C b)<=L*`|a-b|) /\
    (forall t,C (t+(@CircularTrigonometry.half_period R+@CircularTrigonometry.half_period R))=C t) /\
    (forall a b,0<=a ->a<2* @CircularTrigonometry.half_period R ->
      0<=b ->b<2* @CircularTrigonometry.half_period R ->C a=C b ->a=b) /\
    C @` (`[0,2* @CircularTrigonometry.half_period R[:set R)=closure S `\` interior S.
Proof.
move=>[a ha] hOpen hConvex hBound.
pose V:=R_n R 2.
pose hB:=@euclidean_inner_productP R 2.
pose E:=inner_metric_space hB.
pose U:set E:=(fun x:V=>x+a) @^-1` S.
have hOpenU:open U.
  rewrite openE=>x hx.
  apply:(@inner_translation_neighbourhood R V (@euclidean_inner_product R 2) hB a x S).1.
  exact:(open_nbhs_nbhs (conj hOpen hx)).
have hConvexU:is_inner_convex U:=@convex_translate_to_origin R V S a hConvex.
have hZeroU:U 0 by change (S (0+a));rewrite add0r.
have [r [hr hRadius]]:=@metric_bounded_distance_bound R E S a hBound.
have hSubset:U `<=` metric_closed_ball (0:E) r.
  move=>x hx;have hh:=hRadius (x+a) hx.
  have hDistance:=@inner_translation_distance R V (@euclidean_inner_product R 2) hB a 0 x.
  rewrite add0r in hDistance.
  change (is_true (mdist (0:E) x<=r));by rewrite -hDistance.
have hBoundU:metric_set_bounded U.
  exact:(metric_bounded_subset hSubset (@covering_closed_ball_bounded R E 0 r hr)).
have hOpenN:=(@inner_own_norm_open_iff R V (@euclidean_inner_product R 2) hB U).1 hOpenU.
have hBoundN:=(@inner_own_norm_bounded_iff R V (@euclidean_inner_product R 2) hB U).1 hBoundU.
have [C0 [L [hL [hLipschitz [hPeriod [hInjective hImage]]]]]]:=
  @convex_radial_circular_curve_exists R U hOpenN hConvexU hZeroU hBoundN.
rewrite -(@inner_own_norm_boundary R V (@euclidean_inner_product R 2) hB U) in hImage.
pose C:R->E:=fun t=>C0 t+a.
exists C,L;split=>//;split.
- move=>t u;rewrite /C (@inner_translation_distance R V (@euclidean_inner_product R 2) hB a (C0 t) (C0 u)).
  exact:hLipschitz.
split.
- by move=>t;rewrite /C hPeriod.
split.
- move=>t u ht htP hu huP hEqual;apply:hInjective=>//.
  apply:(addIr a);exact hEqual.
- rewrite -(@inner_translation_boundary_image R V (@euclidean_inner_product R 2) hB S a).
  rewrite -hImage;apply/seteqP;split=>y.
  + move=>[t ht <-];exists (C0 t);last exact:erefl;by exists t.
  + move=>[x [t ht hX] hY];exists t=>//;by rewrite /C hX.
Qed.
