(** Federer (1969), 4.1.11, p. 366: affine
    images of the original whole-space Cartesian products.
    Reuse the full smooth product-image theorem and
    actual map agreement, retaining every proof parameter
    of the affine-map interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanAffineSmooth CurrentSpaces CurrentCartesianAffineMap CurrentCartesianMapClass
  CurrentCartesianMapPullback CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentJoinAffineSourcePushforward CurrentAmbientCartesianProduct CurrentAmbientProductPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientAffineProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m mu n nu:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (A:R_n R m->R_n R n) (B:R_n R mu->R_n R nu).
Hypothesis hA:is_affine_map A.
Hypothesis hB:is_affine_map B.
Local Notation AGlobal := (@euclidean_affine_map_smooth R m n (Full m) (hFull m) A hA).
Local Notation BGlobal := (@euclidean_affine_map_smooth R mu nu (Full mu) (hFull mu) B hB).
Local Notation L := (@euclidean_cartesian_map R m mu n nu A B).
Local Notation hL := (@current_cartesian_affine_map R m mu n nu A B hA hB).
Local Notation LGlobal := (@euclidean_affine_map_smooth R (m+mu)%N (n+nu)%N
  (Full (m+mu)%N) (hFull (m+mu)%N) L hL).
Local Notation LClass := (@current_cartesian_factor_open_class R (m+mu)%N (n+nu)%N
  (Full (m+mu)%N) (hFull (m+mu)%N) L LGlobal).
Local Notation ProductClass := (@current_cartesian_map_smooth R m mu n nu A B AGlobal BGlobal).
Local Notation Image := (fun (x:R_n R (m+mu)%N) (_:True)=>Logic.I).
Variables i j:nat.
Variable S:@current_space R h2 m (Full m) (hFull m) i.
Variable T:@current_space R h2 mu (Full mu) (hFull mu) j.
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R mu)))
  (@current_support R h2 mu (Full mu) (hFull mu) j T).
Local Notation Product := (@current_ambient_cartesian_product R h2 m mu i j S T).
Local Notation hProduct := (@current_ambient_cartesian_product_compact R h2 m mu i j S T hS hT).

(** Source for [current_ambient_affine_product]: the
    original (A times B)#(S times T) equals A#S
    times B#T, supporting the prism parametrisation in
    Federer 4.1.11, p. 366. A and B may be
    singular and the current factors need only be compact. *)
Theorem current_ambient_affine_product:
  @current_join_affine_current R h2 (m+mu)%N (n+nu)%N L hL (i+j)%N Product hProduct=
  @current_ambient_cartesian_product R h2 n nu i j
    (@current_join_affine_current R h2 m n A hA i S hS)
    (@current_join_affine_current R h2 mu nu B hB j T hT).
Proof.
have hNatural:=@current_ambient_product_pushforward R h2 m mu n nu A B AGlobal BGlobal
  i j S T hS hT.
have hCompare:=@current_compact_map_images_agree R h2 (m+mu)%N (n+nu)%N
  (Full (m+mu)%N) (Full (n+nu)%N) (hFull (m+mu)%N) (hFull (n+nu)%N)
  L Image LClass (i+j)%N Product hProduct L Image ProductClass hProduct (fun _ _=>erefl).
exact:(eq_trans hCompare hNatural).
Qed.
End CurrentAmbientAffineProduct.
