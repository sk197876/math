(** Federer (1969), 3.3.6, p. 293: original cone heights,
    actual projected balls and their exact countable packing sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureConeHeight StructureConeFreeRemainder
  EuclideanMetricSeparability MetricClosedBalls IndexedBallSelection IndexedDilatedBallVolume
  EuclideanBallVolume NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projected_cone_packing]: the choice of the
    original countable D, projected covering and sum bound in Federer
    3.3.6, p. 293. Each height obeys its independent exact supremum
    laws. Original source indices remain even with coincident projected
    centres; no injectivity of the original projection is assumed. *)
Theorem structure_projected_cone_packing (R:realType) n m (hmn:(m<=n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (e rho:R)
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  0<e ->0<rho ->
  (forall x y,B x ->B y ->mdist x y<= 2*rho/e) ->
  (forall x,B x ->mdist
    (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p x)<=rho) ->
  exists (h:inner_metric_space (@euclidean_inner_productP R n)->R)
    (D:set (inner_metric_space (@euclidean_inner_productP R n))),
    (forall x,structure_active_cone_points hmn B p e x ->
      is_structure_cone_height hmn B p e x (h x) /\h x<= 2*rho/e) /\
    D `<=` structure_active_cone_points hmn B p e /\countable D /\
    (forall x,structure_active_cone_points hmn B p e x ->
      exists i,D i /\mdist
        (euclidean_projection_linear p i:inner_metric_space (@euclidean_inner_productP R m))
        (euclidean_projection_linear p x)<=e*h i) /\
    (nonnegative_sum D (fun i=>(euclidean_unit_ball_volume R m*(e*h i)^+m)%:E)<=
      (7^+m*euclidean_unit_ball_volume R m*rho^+m)%:E)%E.
Proof.
move=>he hRho hDiameter hProjection.
pose C:=structure_active_cone_points hmn B p e.
have hLocal x:exists t,C x ->is_structure_cone_height hmn B p e x t /\t<= 2*rho/e.
  case:(pselect (C x))=>[hx|hNot]; last by exists 0=>/hNot.
  have hBound y:B y ->mdist x y<= 2*rho/e:=hDiameter x y hx.1.
  have [t ht]:=@structure_cone_height_exists R n m hmn B p e x (2*rho/e) he hx.2 hBound.
  exists t=>_; split; first exact:ht.
  apply:(structure_cone_height_least ht)=>y [hy _]; exact:hBound y hy.
have [h hHeight]:=choice hLocal.
pose c:inner_metric_space (@euclidean_inner_productP R n)->
  inner_metric_space (@euclidean_inner_productP R m):=euclidean_projection_linear p.
pose r x:=e*h x/5.
have hPositive x:C x ->0<r x.
  move=>hx; have hNumerator:0<e*h x:=mulr_gt0 he (structure_cone_height_positive (hHeight x hx).1).
  by rewrite /r divr_gt0 // ltr0n.
have hBound:exists M:R,forall x,C x ->r x<=M.
  exists (2*rho/5)=>x hx.
  have hH: h x<= 2*rho/e:=(hHeight x hx).2.
  have hMul:e*h x<= 2*rho.
    have hE:e*(2*rho/e)= 2*rho by rewrite mulrCA mulfV ?gt_eqF ?mulr1.
    have hCompare:e*h x<=e*(2*rho/e) by rewrite ler_pM2l.
    by rewrite hE in hCompare.
  rewrite /r; lra.
have [D [hDC [hCount [hDisjoint [hInject hCover]]]]]:=
  @indexed_bounded_radius_disjoint_fivefold_cover R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) C c r
    (euclidean_metric_separable R m) hPositive hBound.
have hCovered x:C x ->exists i,D i /\mdist (c i) (c x)<=e*h i.
  move=>hx; have hImage:(c @` C) (c x) by exists x.
  have [i hi hNear]:=hCover (c x) hImage.
  exists i; split; first exact:hi.
  have hScale:5*r i=e*h i by rewrite /r; lra.
  change (is_true (mdist (c i) (c x)<= 5*r i)) in hNear.
  by rewrite hScale in hNear.
have hContaining i:D i ->metric_closed_ball (c i) (r i) `<=`
    metric_closed_ball (c a) (7*rho/5).
  move=>hi z hNear.
  have hCi:=hDC i hi.
  have hProjected:mdist (c a) (c i)<=rho:=hProjection i hCi.1.
  have hSmall:r i<= 2*rho/5.
    have hH: h i<= 2*rho/e:=(hHeight i hCi).2.
    have hE:e*(2*rho/e)= 2*rho by rewrite mulrCA mulfV ?gt_eqF ?mulr1.
    have hCompare:e*h i<=e*(2*rho/e) by rewrite ler_pM2l.
    rewrite hE in hCompare; rewrite /r; lra.
  have hTriangle:=metric_triangle (c a) (c i) z.
  change (is_true (mdist (c i) z<=r i)) in hNear.
  change (is_true (mdist (c a) z<= 7*rho/5)); lra.
have hNonnegative i:D i ->0<=r i by move=>hi; exact:ltW (hPositive i (hDC i hi)).
have hOuter:0<= 7*rho/5 by nra.
have hFive:(0:R)<= 5 by rewrite ler0n.
have hVolume:=@euclidean_disjoint_dilated_ball_volume_bound R m
  (inner_metric_space (@euclidean_inner_productP R n)) D c r (c a) (7*rho/5) 5
  hCount hNonnegative hOuter hFive hDisjoint hContaining.
have hRadii i:5*r i=e*h i by rewrite /r; lra.
have hOuterScale:5*(7*rho/5)= 7*rho by lra.
have hCosts:(fun i=>(euclidean_unit_ball_volume R m*(5*r i)^+m)%:E)=
    (fun i=>(euclidean_unit_ball_volume R m*(e*h i)^+m)%:E).
  apply:funext=>i; by rewrite hRadii.
rewrite hCosts hOuterScale exprMn mulrCA mulrA in hVolume.
exists h,D; split; first exact:hHeight.
split; first exact:hDC.
split; first exact:hCount.
split; first exact:hCovered.
exact:hVolume.
Qed.
