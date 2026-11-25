(** Federer (1969), 3.2.23, p. 260: Borel rectangles and
    compact product image pieces under the usual block identification. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap TopologicalBorel
  ProductBorelRectangles ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_cartesian_set_join_image]: the ordinary
    Cartesian set under the usual isomorphism of 2.6.5, p. 120,
    supporting the product theorem 3.2.23, p. 260. *)
Lemma euclidean_cartesian_set_join_image (R:realType) n v
    (A:set (R_n R n)) (B:set (R_n R v)):
  euclidean_cartesian_set A B=(@euclidean_block_join R n v) @` (A `*` B).
Proof.
apply/seteqP; split.
- move=>p hp; exists (euclidean_block_split p); first exact hp.
  exact:euclidean_block_splitK.
- move=>p [[x y] [hx hy] <-].
  change (A (euclidean_block_split (euclidean_block_join (x,y))).1 /\
    B (euclidean_block_split (euclidean_block_join (x,y))).2).
  by rewrite euclidean_block_joinK; split.
Qed.

(** Source for [euclidean_cartesian_compact]: compact product
    parameter sets for the area calculation in Federer 3.2.23,
    p. 260, through compact rectangles and the continuous block map. *)
Lemma euclidean_cartesian_compact (R:realType) n v
    (A:set (R_n R n)) (B:set (R_n R v)):
  @compact (inner_metric_space (@euclidean_inner_productP R n)) A ->
  @compact (inner_metric_space (@euclidean_inner_productP R v)) B ->
  @compact (inner_metric_space (@euclidean_inner_productP R (n+v))) (euclidean_cartesian_set A B).
Proof.
move=>hA hB; rewrite euclidean_cartesian_set_join_image.
exact:(continuous_compact (continuous_subspaceT (@euclidean_block_join_continuous R n v))
  (compact_setX hA hB)).
Qed.

(** Source for [euclidean_cartesian_borel]: the Borel product
    in the statement and proof of Federer 3.2.23, p. 260,
    using the actual Euclidean topology rather than a newly chosen carrier. *)
Lemma euclidean_cartesian_borel (R:realType) n v
    (A:set (R_n R n)) (B:set (R_n R v)):
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) A ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R v)) B ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R (n+v))) (euclidean_cartesian_set A B).
Proof.
move=>hA hB.
exact:(continuous_borel_preimage (@euclidean_block_split_continuous R n v)
  (borel_product_rectangle hA hB)).
Qed.

(** Source for [euclidean_cartesian_map_injective_on]: supporting
    univalence of f times g on A times B in Federer 3.2.23,
    p. 260. Each factor need be univalent only on its actual set. *)
Lemma euclidean_cartesian_map_injective_on (R:realType) m mu n v
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R v)
    (A:set (R_n R m)) (B:set (R_n R mu)):
  (forall x y,A x ->A y ->f x=f y ->x=y) ->
  (forall x y,B x ->B y ->g x=g y ->x=y) ->
  forall p q,euclidean_cartesian_set A B p ->euclidean_cartesian_set A B q ->
    euclidean_cartesian_map f g p=euclidean_cartesian_map f g q ->p=q.
Proof.
move=>hF hG p q [hpA hpB] [hqA hqB] hValue.
have hCoordinates:=congr1 (@euclidean_block_split R n v) hValue.
rewrite !euclidean_cartesian_map_coordinates in hCoordinates.
have hFirst:=hF _ _ hpA hqA (congr1 fst hCoordinates).
have hLast:=hG _ _ hpB hqB (congr1 snd hCoordinates).
apply:(can_inj (@euclidean_block_splitK R m mu)).
by rewrite (surjective_pairing (euclidean_block_split p))
  (surjective_pairing (euclidean_block_split q)) hFirst hLast.
Qed.
