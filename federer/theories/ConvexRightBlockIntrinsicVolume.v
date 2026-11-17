(** Iterated coordinate contraction for the sharp comparison
    in Federer (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates EuclideanRightBlockProjection EuclideanCoordinateSplit EuclideanAffineImageGeometry ScalarConvexLength
  IntegralGeometricGauge ConvexCoordinateTailIntrinsicVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_right_block_intrinsic_volume]:
    supporting arbitrary-codimension coordinate comparison for
    Federer 3.2.45, pp. 279–280.
    Remove the first coordinate repeatedly, retaining
    the original fixed positive intrinsic degree.
    The actual final coordinate block agrees with
    the book's second-coordinate map. The empty
    removed block is the identity; thin bodies
    are retained throughout. *)
Theorem convex_right_block_intrinsic_volume (R : realType) l m k (hKM : (k.+1<=m)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R (l+m)))) :
  K !=set0 -> compact K -> is_inner_convex K ->
  @integral_geometric_gauge R m k.+1 hKM 1 ((@euclidean_right_block R l m) @` K) <=
  @integral_geometric_gauge R (l+m) k.+1 (leq_trans hKM (leq_addl l m)) 1 K.
Proof.
elim: l K=> [|l hInduction] K hNonempty hCompact hConvex.
- have hIdentity : @euclidean_right_block R 0 m=id.
    apply: funext=> x; apply/ffunP=> i.
    rewrite /euclidean_right_block /euclidean_block_split /= ffunE.
    congr (x _); exact: val_inj.
  have hProof : leq_trans hKM (leq_addl 0 m)=hKM := Prop_irrelevance _ _.
  by rewrite hIdentity image_id hProof.
- pose p : {linear R_n R (l+m).+1 -> R_n R (l+m)} :=
    GRing.Linear.clone _ _ _ _ (@coordinate_tail R (l+m)) _.
  have hN : p @` K !=set0.
    have [x hx] := hNonempty; exists (p x); by exists x.
  have hC : @compact [the topologicalType of inner_metric_space (@euclidean_inner_productP R (l+m))] (p @` K).
    have h := @euclidean_affine_hom_compact_image R (l+m).+1 (l+m)
      (hom_of_linear p) (0%R : inner_metric_space (@euclidean_inner_productP R (l+m))) K hCompact.
    have hFunction : (fun x : inner_metric_space (@euclidean_inner_productP R (l+m).+1) =>
        0+hom_of_linear p x)%R=
      (p : inner_metric_space (@euclidean_inner_productP R (l+m).+1) ->
        inner_metric_space (@euclidean_inner_productP R (l+m))).
      apply: funext=> x; by rewrite hom_of_linearE add0r.
    by rewrite hFunction in h.
  have hV : is_inner_convex (p @` K) := linear_image_inner_convex hConvex.
  have hFirst := hInduction (p @` K) hN hC hV.
  have hSecond := @convex_coordinate_tail_intrinsic_volume R (l+m) k
    (leq_trans hKM (leq_addl l m)) K hNonempty hCompact hConvex.
  have hBlock : (@euclidean_right_block R l m) @` (p @` K)=
      (@euclidean_right_block R l.+1 m) @` K.
    rewrite image_comp; congr (_ @` K); apply: funext=> x; apply/ffunP=> i.
    rewrite /euclidean_right_block /euclidean_block_split /p /coordinate_tail /= !ffunE.
    congr (x _); apply: val_inj; by rewrite /= ?lift0 ?addnS ?addSn.
  rewrite hBlock in hFirst.
  have hProof : leq_trans (leq_trans hKM (leq_addl l m)) (leqnSn (l+m))=
      leq_trans hKM (leq_addl l.+1 m) := Prop_irrelevance _ _.
  rewrite hProof in hSecond.
  exact: le_trans hFirst hSecond.
Qed.
