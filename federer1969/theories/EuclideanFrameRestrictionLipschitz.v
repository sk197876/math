(** Federer (1969), 3.2.28(3), pp. 265–266:
    the actual linear forgetful map satisfies the
    Lipschitz prerequisite of 3.2.22. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts EuclideanFrameRestriction NormDifferentialUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_frame_restriction_lipschitz]:
    the Lipschitz bound for S in the coarea application,
    Federer 3.2.28(3), p. 266. A finite
    homogeneous bound follows from its actual full
    differential, already proved in the finite Hom norm.
    This supporting bound holds on every subset and
    does not require alpha to be orthogonal. *)
Lemma euclidean_frame_restriction_lipschitz (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) (S:set (Hom (R_n R m) (R_n R n))):
  exists L,@is_metric_lipschitz_bound R (inner_metric_space (@euclidean_hom_inner_productP R m n))
    (inner_metric_space (@euclidean_hom_inner_productP R k n)) S
    (@euclidean_frame_restriction R k m n alpha) L.
Proof.
have [L [hL hBound]]:=norm_differential_bounded
  (@euclidean_frame_restriction_differential R k m n alpha 0).
exists L; split; first exact hL.
move=>x y _ _; rewrite !inner_metric_distanceE.
change (is_true (inner_norm (@euclidean_hom_inner_productP R k n)
  (euclidean_frame_restriction n alpha x-euclidean_frame_restriction n alpha y)<=
  L*inner_norm (@euclidean_hom_inner_productP R m n) (x-y))).
rewrite -linearB; exact:hBound.
Qed.
