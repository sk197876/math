(** Federer (1969), 4.1.4, p. 348: identify the positive
    ball-margin specification with the original distance
    inequality. The existing distance interface is used only
    for a nonempty complement; its infimum laws prove both
    implications, with no attainment hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric MetricSetDistanceUP MetricSetDistanceSealed InnerParallelFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_parallel_distance_characterization]: the
    independently specified inward locus is exactly the original
    A intersect {distance to complement > e}, Federer 4.1.4,
    p. 348, whenever that original real distance exists. *)
Theorem inner_parallel_distance_characterization (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (O:R->set X)
    (d:real_norm_metric_space hNX->R):
  is_inner_parallel_family NX A O ->
  @is_metric_set_distance R (real_norm_metric_space hNX) (~` A) d ->
  forall e:R,0<e ->forall x:X,O e x <-> A x /\ e<d x.
Proof.
move=>hO hD e he x; split.
- move=>hx; have[hAx [r [her hBall]]]:=(@hO e he x).1 hx.
  split=>//.
  have hLower:r<=d x.
    apply:(@metric_set_distance_greatest R (real_norm_metric_space hNX) (~` A) d hD x r)=>y hy.
    rewrite leNgt; apply/negP=>hSmall; apply:hy; apply:hBall.
    change (is_true (NX (x-y)<r)) in hSmall.
    by rewrite (real_seminorm_subtract hNX.1).
  exact:lt_le_trans her hLower.
- move=>[hx hED]; apply:(@hO e he x).2; split=>//.
  pose r:=(e+d x)/2.
  have hER:e<r by rewrite /r; lra.
  have hRD:r<d x by rewrite /r; lra.
  exists r; split=>// y hy.
  apply:contrapT=>hNot.
  have hBound:=@metric_set_distance_lower R (real_norm_metric_space hNX) (~` A) d hD x y hNot.
  change (is_true (d x<=NX (x-y))) in hBound.
  rewrite (real_seminorm_subtract hNX.1) in hBound.
  have hContra:=le_lt_trans hBound (lt_trans hy hRD).
  by move:hContra; rewrite ltxx.
Qed.

(** Source for [inner_parallel_original_distance]: the actual
    opaque distance to the nonempty complement gives precisely
    Federer's original inward locus, 4.1.4, p. 348. *)
Theorem inner_parallel_original_distance (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (O:R->set X)
    (hNonempty:(~` A)!=set0):
  is_inner_parallel_family NX A O ->
  forall e:R,0<e ->forall x:X,O e x <->
    A x /\ e<@MetricSetDistance.value R (real_norm_metric_space hNX) (~` A) hNonempty x.
Proof.
move=>hO.
exact:(@inner_parallel_distance_characterization R X NX hNX A O _
  hO (@MetricSetDistance.laws R (real_norm_metric_space hNX) (~` A) hNonempty)).
Qed.
