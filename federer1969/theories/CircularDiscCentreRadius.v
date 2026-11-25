(** Federer (1969), 3.3.19, p. 303: every
    actual child centre is on the original radial
    retraction sphere. Prove its exact distance from
    the original parent centre from the printed formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric CircularUnitVectors CircularDiscRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [circular_disc_child_centre_radius]: exact
    original distance r-r/n of a child centre
    from its original parent centre, supporting
    E=B(z,r-r/n) in 3.3.19, p. 303.
    Every positive subdivision n and nonnegative r remain. *)
Lemma circular_disc_child_centre_radius (R:realType)
    (z:inner_metric_space (@euclidean_inner_productP R 2)) (r:R) n (k:'I_n):
  0<=r ->(0<n)%N ->mdist z (circular_disc_child_center z r k)=r-r/n%:R.
Proof.
move=>hr hn.
have hN1:(1<=n%:R:>R) by rewrite ler1n.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hInv:(0<n%:R^-1:>R) by rewrite invr_gt0.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hBudget:(n%:R:R)*n%:R^-1= 1 by rewrite mulfV.
have hScale:0<=(1-n%:R^-1)*r by nra.
rewrite metric_sym inner_metric_distanceE /circular_disc_child_center addrAC subrr add0r
  inner_normZ circular_unit_vector_norm mulr1 (ger0_norm hScale);ring.
Qed.
