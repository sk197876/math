(** Federer (1969), 3.2.29, p. 268:
    the full-rank image is the union of a
    countable family of class-one m-dimensional manifolds. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormRegularity NormClassOneUP LinearRankAtLeast EuclideanSubmanifoldUP
  FullRankLocalManifoldImage EuclideanLebesgueHaar CountableBaseLindelof.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [full_rank_countable_manifold_images]:
    the countable family G of local images in
    Federer 3.2.29, p. 268. The ambient
    Euclidean countable base selects open domains
    inside P, so their actual images cover f(P)
    exactly, without a global embedding assumption. *)
Theorem full_rank_countable_manifold_images (R:realType) m n
    (f:R_n R m->R_n R n) (D:R_n R m->Hom (R_n R m) (R_n R n)):
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f 1 ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f D ->
  exists C:set (set (R_n R n)),countable C /\
    (forall S,C S ->@is_euclidean_submanifold R n m 1 S) /\
    f @` [set x|linear_rank_at_least (D x) m]=\bigcup_(S in C) S.
Proof.
move=>hF hD.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose P:set X:=[set x|linear_rank_at_least (D x) m].
pose A:set (set X):=[set U|open U /\U `<=` P /\@is_euclidean_submanifold R n m 1 (f @` U)].
have hCover:P `<=` \bigcup_(U in A) U.
  move=>a ha; have [U [hUa [hU [hUP hMan]]]]:=full_rank_local_manifold_image hF hD ha.
  exists U; last exact hUa; split; first exact hU; by split.
have [B hB]:=euclidean_countable_open_base R m.
have [G [hGA [hGC hPG]]]:=@countable_base_open_subcover [the topologicalType of X] B P A hB
  (fun U hU=>hU.1) hCover.
exists ((fun U:set X=>f @` U) @` G); split.
- exact:sub_countable (card_image_le _ _) hGC.
- split.
  + move=>S [U hUG <-]; exact:(hGA U hUG).2.2.
  + apply/seteqP; split=>y.
    * move=>[x hx <-]; have [U hUG hxU]:=hPG x hx.
      exists (f @` U); first by exists U.
      by exists x.
    * move=>[S [U hUG <-] [x hx <-]].
      exists x; last reflexivity; exact:(hGA U hUG).2.1 x hx.
Qed.
