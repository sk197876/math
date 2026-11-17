(** Federer (1969), 3.4.12, p. 339: the exact real
    coordinate identification preserves the all-subset growth estimate.
    Reuse the existing bijective Hausdorff isometry theorem and
    metric diameter invariance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import UniformHausdorffGrowthUP CoveringFamilyUP MetricDiameter
  HausdorffMeasure HausdorffIsometricBijection MetricIsometricImageGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_hausdorff_growth_isometric_image]: transfer
    the real-case diameter estimate to the original complex metric,
    as required by 3.4.12, p. 339. Every subset and
    every natural degree, including zero, retains the same bound. *)
Theorem uniform_hausdorff_growth_isometric_image (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X) m (S:set X) (c:R):
  cancel f g ->cancel g f ->(forall x y,mdist (f x) (f y)=mdist x y) ->
  is_uniform_hausdorff_growth m S c ->is_uniform_hausdorff_growth m (f @` S) c.
Proof.
move=>hGF hFG hMetric hGrowth.
have hInverseMetric (x y:Y):mdist (g x) (g y)=mdist x y.
  by rewrite -(hMetric (g x) (g y)) !hFG.
constructor.
- rewrite /metric_set_bounded (metric_isometric_image_diameter hMetric).
  exact:uniform_hausdorff_growth_bounded hGrowth.
- exact:uniform_hausdorff_growth_coefficient hGrowth.
- move=>A hAS.
  have hGA:g @` A `<=` S.
    move=>x [y hy <-];have [z hz hEqual]:=hAS y hy.
    by rewrite -hEqual hGF.
  have hBack:f @` (g @` A)=A.
    apply/seteqP;split.
    + move=>x [y [z hz <-] <-];by rewrite hFG.
    + move=>x hx;exists (g x);first by exists x.
      exact:hFG.
  have hEstimate:=@uniform_hausdorff_growth_bound R X m S c hGrowth (g @` A) hGA.
  rewrite (metric_isometric_image_diameter hInverseMetric) in hEstimate.
  have hMeasure:=@hausdorff_bijective_isometry_invariance R X Y f g hGF hFG hMetric m (g @` A).
  by rewrite hBack in hMeasure;rewrite hMeasure.
Qed.
