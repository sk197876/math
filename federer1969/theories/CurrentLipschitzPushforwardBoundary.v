(** Federer (1969), 4.1.14, p. 371: the
    opaque original local image commutes with
    positive-degree boundary. Its public law and
    the previously proved candidate boundary theorem
    identify the two actual currents. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces CurrentBoundary CurrentProperSupport FlatCurrentsUP
  CurrentLocallyFlatBoundary CurrentLipschitzPushforwardSealed CurrentLipschitzImageBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_lipschitz_pushforward_boundary]:
    boundary(f#T)=f#(boundary T), Federer 4.1.14,
    p. 371. The support properness of
    boundary T follows from that of T
    by the preceding support inclusion; arbitrary
    evidence of that derived fact is admitted. *)
Theorem current_lipschitz_pushforward_boundary
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (T:@current_space R h2 n U hU m.+1)
    (hT:@is_locally_flat_current R h2 n m.+1 U hU T)
    (hProper:@is_current_proper_on_support R h2 n nu m.+1 U hU V T f hImage)
    (hProperBoundary:@is_current_proper_on_support R h2 n nu m U hU V
      (@current_boundary R h2 n m U hU T) f hImage):
  @current_boundary R h2 nu m V hV
    (@CurrentLipschitzPushforward.value R h2 n nu m.+1 U V hU hV
      f hImage hLocal T hT hProper)=
  @CurrentLipschitzPushforward.value R h2 n nu m U V hU hV f hImage hLocal
    (@current_boundary R h2 n m U hU T)
    (@locally_flat_current_boundary R h2 n m U hU T hT) hProperBoundary.
Proof.
exact:(@current_lipschitz_image_boundary R h2 n nu m U V hU hV
  f hImage hLocal T _ _ hT hProper
  (@CurrentLipschitzPushforward.laws R h2 n nu m.+1 U V hU hV
    f hImage hLocal T hT hProper)
  (@CurrentLipschitzPushforward.laws R h2 n nu m U V hU hV f hImage hLocal
    (@current_boundary R h2 n m U hU T)
    (@locally_flat_current_boundary R h2 n m U hU T hT) hProperBoundary)).
Qed.
