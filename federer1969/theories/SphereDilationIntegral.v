(** Federer (1969), 3.2.13, p. 250: exact
    integral change from a radius-r sphere
    to the unit sphere, including signed infinite
    values and the actual partial integrand domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  SphereDilationMeasure HausdorffMeasure MeasureUP MeasureRestriction MeasurePushforward MeasureScaleIntegral
  PushforwardMeasurabilityTransfer PushforwardIntegral PartialFunctionUP PartialFunctionPrecomposition
  MeasureIntegralUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sphere_dilation_integral_iff]: the unit-sphere
    substitution underlying the second polar identity,
    Federer 3.2.13, p. 250. Its
    exact graph equivalence retains undefined inner integrals;
    the coefficient is positive even in degree zero. *)
Lemma sphere_dilation_integral_iff (R:realType) m k (r:R)
    (u:partial_function (R_n R m) (extended_real_line R)) a:
  (0<r)%R ->
  (is_measure_integral (spherical_hausdorff_measure m k r) u a <->
    is_measure_integral (spherical_hausdorff_measure m k (1%R:R))
      (partial_function_precompose (fun x:R_n R m=>r*:x) u) (((r^+k)^-1)%R%:E*a)).
Proof.
move=>hr.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=spherical_hausdorff_measure m k (1%R:R).
pose hmu:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X k)
  [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R].
pose d (x:X):=r*:x.
pose nu:=measure_pushforward d mu.
have hNu:is_measure nu:=measure_pushforward_is_measure d hmu.
pose c:=(r^+k)%R.
have hc:(0<c)%R:=exprn_gt0 k hr.
have hcInv:(0<c^-1)%R by rewrite invr_gt0.
have hcNe:(c!= 0)%R:=lt0r_neq0 hc.
have hMeasure:spherical_hausdorff_measure m k r=measure_scale c nu.
  exact:spherical_hausdorff_dilation_pushforward hr.
have hInjective:injective d.
  move=>x y he.
  have hh:=congr1 (fun z:X=>r^-1*:z) he.
  by rewrite /d !scalerA mulVf ?(lt0r_neq0 hr) // !scale1r in hh.
split.
- move=>hI; rewrite hMeasure in hI.
  have hScaled:=@measure_scale_integral R X (measure_scale c nu)
    (measure_scale_is_measure hNu hc) c^-1 hcInv u a hI.
  rewrite (measure_scale_inverse nu hc) in hScaled.
  have hMeas:=measurable_function_pushforward_precompose hInjective hScaled.1.
  exact ((@measure_pushforward_integral_iff R X X mu hmu d u hMeas _).2 hScaled).
- move=>hI.
  have hPushed:=(@measure_pushforward_integral_iff R X X mu hmu d u hI.1 _).1 hI.
  have hScaled:=@measure_scale_integral R X nu hNu c hc u _ hPushed.
  rewrite muleA -EFinM mulfV // mul1e in hScaled.
  by rewrite -hMeasure in hScaled.
Qed.
