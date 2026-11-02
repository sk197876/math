(** Federer (1969), 3.2.28(3), p. 266:
    the actual Stiefel volume recurrence from the
    computed forgetful-map Jacobian and spherical fibres. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps OrthogonalEmbedding EuclideanForgetfulCoareaVolume EuclideanManifoldVolumes
  HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_stiefel_volume_recurrence]: the
    displayed recurrence in Federer 3.2.28(3),
    p. 266, written with (sqrt 2)^k for
    2^(k/2), where m=k+1. A rectangular
    orthogonal alpha exists locally; neither a global
    selected frame nor a volume premise is required. *)
Theorem euclidean_stiefel_volume_recurrence (R:realType) n k:
  (k.+1<=n)%N ->
  euclidean_stiefel_volume R n k.+1=
    ((Num.sqrt (2:R))^+k)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-k))) (n-k-1)
      [set z|inner_norm (@euclidean_inner_productP R (n-k)) z= 1%R]*
    euclidean_stiefel_volume R n k.
Proof.
Local Open Scope ring_scope.
move=>hkn.
have [a hA]:=@orthogonal_embedding_exists R (R_n R k) (R_n R k.+1)
  (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
  (@euclidean_inner_productP R k) (@euclidean_inner_productP R k.+1)
  k (@coordinate_basis R k) (@coordinate_basisP R k)
  k.+1 (@coordinate_basis R k.+1) (@coordinate_basisP R k.+1) (leqnSn k).
have h:=@euclidean_forgetful_coarea_volume R k n (hom_of_linear a) hkn hA.
pose c:=(Num.sqrt (2:R))^+k.
have hc:0<c by rewrite /c exprn_gt0 // sqrtr_gt0 ltr0n.
have hs:Num.sqrt (2:R)!=0 by rewrite gt_eqF // sqrtr_gt0 ltr0n.
have hInv:c*(Num.sqrt (2:R))^-k= 1.
  by rewrite /c -exprVn -exprMn mulfV // expr1n.
have hScaled:=congr1 (fun z : \bar R => c%:E * z)%E h.
rewrite muleA -EFinM hInv mul1e in hScaled.
change (euclidean_stiefel_volume R n k.+1=
  c%:E* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-k))) (n-k-1)
    [set z|inner_norm (@euclidean_inner_productP R (n-k)) z= 1%R]*
  euclidean_stiefel_volume R n k)%E.
rewrite -muleA; exact hScaled.
Qed.
