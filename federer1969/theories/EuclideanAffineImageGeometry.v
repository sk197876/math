(** Federer (1969), 3.2.38, pp. 274--275: actual affine
    images preserve convexity and compactness and retain a proved
    homogeneous Lipschitz bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm InnerConvex
  HilbertFormCompactness HomSpaceTopology LipschitzUP NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_hom_convex_image]: supporting convexity of
    the actual g(K) before Steiner's formula in Federer 3.2.38,
    p. 275. The affine segment identity follows from the exposed
    linear-map laws, without using any private representation. *)
Lemma affine_hom_convex_image (R:realFieldType) (V W:lmodType R)
    (D:Hom V W) (c:W) (Q:set V):
  is_inner_convex Q ->is_inner_convex ((fun x=>c+D x) @` Q).
Proof.
move=>hQ y z [u hu <-] [v hv <-] t ht0 ht1.
exists ((1-t)*:u+t*:v); first exact:hQ u v hu hv t ht0 ht1.
rewrite linearD !linearZ.
by rewrite !scalerDr addrACA -scalerDl subrK scale1r.
Qed.

(** Source for [euclidean_affine_hom_lipschitz_bound]: supporting
    actual affine-image size bounds in Federer 3.2.38, p. 275.
    The earlier opaque operator norm supplies a finite bound for
    every linear map, including singular and zero-dimensional maps. *)
Lemma euclidean_affine_hom_lipschitz_bound (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) (c:inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz_bound setT
    (fun x:inner_metric_space (@euclidean_inner_productP R m)=>c+D x)
    (hom_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
      (@coordinate_basisP R m) D).
Proof.
split; first exact:hom_operator_norm_nonnegative.
move=>x y _ _; rewrite !inner_metric_distanceE.
have hDifference:(c+D x)-(c+D y)=D (x-y).
  by rewrite opprD addrACA subrr add0r linearB.
rewrite hDifference; exact:hom_operator_norm_bound.
Qed.

(** Source for [euclidean_affine_hom_compact_image]: supporting
    actual compactness of g(K) in Federer 3.2.38, p. 275.
    Continuity follows from its proved finite Lipschitz bound;
    no compact-image witness is assumed in the later estimate. *)
Lemma euclidean_affine_hom_compact_image (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) (c:inner_metric_space (@euclidean_inner_productP R n))
    (Q:set (inner_metric_space (@euclidean_inner_productP R m))):
  compact Q ->compact ((fun x=>c+D x) @` Q).
Proof.
move=>hQ.
have hLip:=euclidean_affine_hom_lipschitz_bound D c.
have hContinuous:continuous (fun x:inner_metric_space (@euclidean_inner_productP R m)=>c+D x).
  apply:metric_fixed_lipschitz_continuous; first exact:hLip.1.
  move=>x y; exact:hLip.2 x y Logic.I Logic.I.
apply:continuous_compact=>//; exact:continuous_subspaceT hContinuous.
Qed.
