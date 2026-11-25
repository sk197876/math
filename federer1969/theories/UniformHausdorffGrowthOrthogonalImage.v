(** Federer (1969), 3.4.8(13), p. 336:
    return the uniform diameter estimate from the chosen
    orthogonal coordinates. The existing all-set Hausdorff and
    isometric diameter invariance preserve the same coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  OrthogonalMaps OrthogonalFinite OrthogonalHausdorffImage MetricIsometricImageGeometry
  MetricDiameter CoveringFamilyUP UniformHausdorffGrowthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_hausdorff_growth_orthogonal_image]: the original
    representative may be returned from the chosen g
    coordinates without changing its growth coefficient,
    3.4.8(13), p. 336. *)
Theorem uniform_hausdorff_growth_orthogonal_image (R:realType) n m
    (f:{linear R_n R n->R_n R n}) (S:set (R_n R n)) (c:R):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) f ->
  @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) m S c ->
  @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` S) c.
Proof.
move=>hF hGrowth.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [g [hFG [hGF hG]]]:=@orthogonal_endomorphism_inverse_exists R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) n
  (@coordinate_basis R n) (@coordinate_basisP R n) f hF.
have hDistance (u:{linear R_n R n->R_n R n})
    (hU:is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) u)
    (x y:X):@mdist R X (u x) (u y)=mdist x y.
  by rewrite !inner_metric_distanceE -linearB
    (orthogonal_map_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) hU).
constructor.
- rewrite /metric_set_bounded (metric_isometric_image_diameter (hDistance f hF)).
  exact:uniform_hausdorff_growth_bounded hGrowth.
- exact:uniform_hausdorff_growth_coefficient hGrowth.
- move=>T hTS.
  have hGT:g @` T `<=` S.
    move=>x [y hy <-];have [z hz hEqual]:=hTS y hy.
    by rewrite -hEqual hFG.
  have hImage:f @` (g @` T)=T.
    apply/seteqP;split.
    + move=>x [y [z hz <-] <-];by rewrite hGF.
    + move=>x hx;exists (g x);first by exists x.
      exact:hGF.
  have hMass:=@uniform_hausdorff_growth_bound R X m S c hGrowth (g @` T) hGT.
  rewrite (metric_isometric_image_diameter (hDistance g hG)) in hMass.
  have hMeasure:=@hausdorff_orthogonal_image R n m f (g @` T) hF.
  by rewrite hImage in hMeasure;rewrite hMeasure.
Qed.
