(** Federer (1969), 4.1.18, pp. 375–376:
    q maps onto the whole original F_m(U). Choose
    a positive tube for the given compact flat index
    and use the quantitative original-U representation.
    No selected index is part of the opaque map. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces FlatCurrentsUP CurrentLonePairImageUP
  CurrentCompactClosedTubeInside CurrentFlatLonePairRepresentation
  FlatCurrentUnionSpace CurrentLonePairFlatSealed CurrentLonePairFlatLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_lone_pair_flat_surjective]: every
    original flat current has an actual compact L1 pair
    preimage, Federer 4.1.18, pp. 375–376. Empty U,
    zero ambient dimension and every current degree remain. *)
Theorem current_lone_pair_flat_surjective (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
  forall T,exists v,@CurrentLonePairFlat.map R h2 n m U hU v=T.
Proof.
move=>T.
have[K hFlat]:=@flat_current_union_inclusion_member R h2 n m U hU T.
have[delta [hDelta hInside]]:=@current_compact_closed_tube_inside_exists R n U hU K.
have[v [hValue _]]:=@current_flat_lone_pair_representation R h2 n m U hU
  K (@flat_current_union_inclusion R h2 n m U hU T) delta hFlat hDelta hInside.
exists v;apply:(@flat_current_union_inclusion_injective R h2 n m U hU).
by rewrite current_lone_pair_flat_value.
Qed.
