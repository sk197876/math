(** Federer (1969), 2.6.5, p. 120: the usual isomorphism R^(m+n) to R^m
    times R^n. The left block consists of the first m coordinates and the
    right block of the final n coordinates. These maps use the existing
    Euclidean dot-product topology and include empty blocks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNormedTopology ConcatenatedFamilies EuclideanCoordinateTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Blocks.
Variable R : realType.
Variables m n : nat.
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).

(** Source for [euclidean_block_join]: inverse of the
    usual block isomorphism in Federer 2.6.5, p. 120,
    concatenating the two ordered coordinate families. *)
Definition euclidean_block_join (p : E m * E n) : E (m+n) :=
  [ffun i => concatenate_family p.1 p.2 i].

(** Source for [euclidean_block_split]: the usual
    isomorphism in Federer 2.6.5, p. 120, with
    first m and final n coordinates as its two factors. *)
Definition euclidean_block_split (x : E (m+n)) : E m * E n :=
  ([ffun i => x (lshift n i)], [ffun j => x (rshift m j)]).

(** Source for [euclidean_block_join_left]: first block
    of the inverse identification, Federer 2.6.5, p. 120. *)
Lemma euclidean_block_join_left p i : euclidean_block_join p (lshift n i) = p.1 i.
Proof. by rewrite /euclidean_block_join ffunE concatenate_family_l. Qed.

(** Source for [euclidean_block_join_right]: second block
    of the inverse identification, Federer 2.6.5, p. 120. *)
Lemma euclidean_block_join_right p j : euclidean_block_join p (rshift m j) = p.2 j.
Proof. by rewrite /euclidean_block_join ffunE concatenate_family_r. Qed.

(** Source for [euclidean_block_joinK]: first inverse
    identity for the usual isomorphism of Federer 2.6.5,
    p. 120, including empty blocks. *)
Lemma euclidean_block_joinK : cancel euclidean_block_join euclidean_block_split.
Proof.
move=> [u v]; rewrite /euclidean_block_split; congr (_,_); apply/ffunP=> i;
  by rewrite ffunE ?euclidean_block_join_left ?euclidean_block_join_right.
Qed.

(** Source for [euclidean_block_splitK]: second inverse
    identity for the usual isomorphism of Federer 2.6.5,
    p. 120. *)
Lemma euclidean_block_splitK : cancel euclidean_block_split euclidean_block_join.
Proof.
move=> x; apply/ffunP=> i; rewrite /euclidean_block_join ffunE /concatenate_family.
case: (splitP i)=> j hij; rewrite /euclidean_block_split /= ffunE;
  congr (x _); apply: val_inj; exact: esym hij.
Qed.

(** Source for [euclidean_block_join_continuous]: supporting
    continuity of the inverse Euclidean block identification
    in Federer 2.6.5, p. 120. *)
Lemma euclidean_block_join_continuous : continuous euclidean_block_join.
Proof.
apply: euclidean_map_continuous=> i.
case hi: (split i)=> [j|j].
- have he : (fun p : E m * E n => euclidean_block_join p i) = (fun p => p.1 j).
    by apply: funext=> p; rewrite /euclidean_block_join ffunE /concatenate_family hi.
  rewrite he=> p.
  apply: (@continuous_comp (Topological.clone (E m * E n)%type _)
    (Topological.clone (E m) _) (Topological.clone R^o _) (@fst (E m) (E n)) (fun x => x j) p).
  + exact: first_projection_continuous.
  + exact (@euclidean_coordinate_continuous R m j p.1).
- have he : (fun p : E m * E n => euclidean_block_join p i) = (fun p => p.2 j).
    by apply: funext=> p; rewrite /euclidean_block_join ffunE /concatenate_family hi.
  rewrite he=> p.
  apply: (@continuous_comp (Topological.clone (E m * E n)%type _)
    (Topological.clone (E n) _) (Topological.clone R^o _) (@snd (E m) (E n)) (fun x => x j) p).
  + exact: second_projection_continuous.
  + exact (@euclidean_coordinate_continuous R n j p.2).
Qed.

(** Source for [euclidean_block_split_continuous]: supporting
    continuity of the usual Euclidean block identification
    in Federer 2.6.5, p. 120. *)
Lemma euclidean_block_split_continuous : continuous euclidean_block_split.
Proof.
apply: topological_pair_continuous.
- apply: euclidean_map_continuous=> i.
  have he : (fun x : E (m+n) => (euclidean_block_split x).1 i) = (fun x => x (lshift n i)).
    by apply: funext=> x; rewrite /euclidean_block_split /= ffunE.
  rewrite he; exact: euclidean_coordinate_continuous.
- apply: euclidean_map_continuous=> j.
  have he : (fun x : E (m+n) => (euclidean_block_split x).2 j) = (fun x => x (rshift m j)).
    by apply: funext=> x; rewrite /euclidean_block_split /= ffunE.
  rewrite he; exact: euclidean_coordinate_continuous.
Qed.
End Blocks.
