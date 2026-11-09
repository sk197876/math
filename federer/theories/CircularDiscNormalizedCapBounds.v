(** Federer (1969), 3.3.19, p. 305: normalized mass
    estimates for the actual original caps, uniformly over
    every parent, original orientation and cap half-angle. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometrySealed
  CircularRegularDirections CircularCapThresholdCounts CircularDiscCaps CircularDiscCapMassBrackets
  CircularDiscTreeUP CircularDiscLimitUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Bounds.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_normalized_cap_bounds]: the
    actual H1 cap mass divided by 2rho_(n-1) is within
    e/pi+1/n of gamma/pi, whenever the proved uniform
    cosine margin dominates 2/n. This is the quantitative
    original-set estimate behind the uniform comparison in
    3.3.19, p. 305, including gamma= 0 and gamma= pi. *)
Theorem circular_disc_normalized_cap_bounds j (z u:E) (e gamma:R):
  z \in H j ->inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  0<e ->e<p ->0<=gamma ->gamma<=p ->
  2/(j+4)%:R<2*(S (e/2))^+2 ->
  (((gamma/p-e/p-1/(j+4)%:R)%:E<=
    mu (A `&` circular_disc_cap z (rho j) u gamma)/(2* rho j)%:E)%E /\
   (mu (A `&` circular_disc_cap z (rho j) u gamma)/(2* rho j)%:E<=
    (gamma/p+e/p+1/(j+4)%:R)%:E)%E).
Proof.
move=>hz hu he hep hGamma hGammaP hSmall.
pose F:= @circular_disc_cap_inner_children R j u gamma.
pose G:= @circular_disc_cap_meeting_children R j z u gamma.
have hn:(0<j+4)%N by rewrite addn_gt0 orbT.
have hInner k:C gamma+2/(j+4)%:R<=euclidean_inner_product (@circular_regular_direction R (j+4)%N k) u ->k \in F.
  move=>hCoordinate;by rewrite /F /circular_disc_cap_inner_children in_fset /=.
have hOuter k:k \in G ->C gamma-2/(j+4)%:R<=euclidean_inner_product (@circular_regular_direction R (j+4)%N k) u.
  move=>hk;exact:(@circular_disc_cap_meeting_child_coordinate R j z u gamma k hu hk).
have hCountLower:= @circular_perturbed_cap_lower_count R (j+4)%N u e gamma F
  hn hu he hep hGamma hGammaP hSmall hInner.
have hCountUpper:= @circular_perturbed_cap_upper_count R (j+4)%N u e gamma G
  hn hu he hep hGamma hGammaP hSmall hOuter.
have [hLower hUpper]:= @circular_disc_original_cap_mass_brackets R H hH A hA j z u gamma hz hu.
have hRadius:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hRadiusN:rho j!=0 by rewrite gt_eqF.
have hDen:0<2* rho j by lra.
have hIndexN:((j+4)%:R:R)!=0 by rewrite pnatr_eq0 addn_eq0 andbF.
have hInverse:(0<=((2* rho j)%:E)^-1)%E by rewrite inve_ge0 lee_fin;exact:ltW hDen.
have hScale (T:{fset 'I_(j+4)}):
    (((2* rho j.+1*#|` T|%:R)%:E/(2* rho j)%:E)=(#|` T|%:R/(j+4)%:R)%:E)%E.
  rewrite inver (gt_eqF hDen) -EFinM;apply:(congr1 (fun x:R=>x%:E)).
  rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R));field.
  have hExpanded:(j%:R+4:R)!=0.
    have hJ0:(0<=j%:R:>R) by rewrite ler0n.
    rewrite gt_eqF //;lra.
  by rewrite hExpanded hRadiusN.
have hNormalizedLower:= lee_wpmul2r hInverse hLower.
have hNormalizedUpper:= lee_wpmul2r hInverse hUpper.
rewrite (hScale (@circular_disc_cap_inner_children R j u gamma)) in hNormalizedLower.
rewrite (hScale (@circular_disc_cap_meeting_children R j z u gamma)) in hNormalizedUpper.
split.
- exact:(le_trans (lee_tofin hCountLower) hNormalizedLower).
- exact:(le_trans hNormalizedUpper (lee_tofin hCountUpper)).
Qed.
End Bounds.
