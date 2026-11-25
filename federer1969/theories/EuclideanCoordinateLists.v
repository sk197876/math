(** Supporting ordered coordinates for the usual isomorphism in Federer
    (1969), 2.6.5, p. 120. Finite coordinate lists compare the canonical
    measure associations with the actual Euclidean block map without
    choosing a different Euclidean carrier. Source context:
    EuclideanBlockCoordinates.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ConcatenatedFamilies EuclideanCoordinateSplit EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_list]: supporting
    ordered list of all Euclidean coordinates in the
    identification of Federer 2.6.5, p. 120. *)
Fixpoint euclidean_coordinate_list (R : realType) n : R_n R n -> seq R :=
  match n as k return R_n R k -> seq R with
  | 0 => fun _ => [::]
  | k.+1 => fun x => coordinate_head x :: @euclidean_coordinate_list R k (coordinate_tail x)
  end.
Arguments euclidean_coordinate_list {R n} x.

(** Source for [euclidean_coordinate_list_enum]: supporting
    agreement with the existing finite-coordinate enumeration
    in Federer 2.6.5, p. 120. *)
Lemma euclidean_coordinate_list_enum (R : realType) n (x : R_n R n) :
  euclidean_coordinate_list x = [seq x i | i <- enum 'I_n].
Proof.
elim: n x=> [x|n ih x]; first by rewrite enum_ord0.
rewrite /= enum_ordSl /= -map_comp; congr (_ :: _).
rewrite ih; apply: eq_map=> i; by rewrite /coordinate_tail ffunE.
Qed.

(** Source for [euclidean_coordinate_list_injective]:
    supporting uniqueness of a Euclidean vector from its
    ordered coordinates in Federer 2.6.5, p. 120. *)
Lemma euclidean_coordinate_list_injective (R : realType) n :
  injective (@euclidean_coordinate_list R n).
Proof.
elim: n=> [x y _|n ih x y he]; first by rewrite (coordinate_zero x) (coordinate_zero y).
have hh : coordinate_head x = coordinate_head y := congr1 (head 0) he.
have ht : coordinate_tail x = coordinate_tail y := ih _ _ (congr1 behead he).
by rewrite -(coordinate_decomposition x) -(coordinate_decomposition y) hh ht.
Qed.

(** Source for [euclidean_block_join_list]: concatenation
    of the two coordinate blocks in the usual isomorphism
    of Federer 2.6.5, p. 120. Empty blocks are included. *)
Lemma euclidean_block_join_list (R : realType) m n
    (p : inner_metric_space (@euclidean_inner_productP R m) * inner_metric_space (@euclidean_inner_productP R n)) :
  euclidean_coordinate_list (euclidean_block_join p) =
    euclidean_coordinate_list p.1 ++ euclidean_coordinate_list p.2.
Proof.
rewrite !euclidean_coordinate_list_enum.
transitivity [seq concatenate_family p.1 p.2 i | i <- enum 'I_(m+n)].
- apply: eq_map=> i; by rewrite /euclidean_block_join ffunE.
- exact: concatenate_family_sequence.
Qed.

(** Source for [euclidean_block_split_list]: the coordinate
    list is split into its two consecutive blocks by the
    usual map of Federer 2.6.5, p. 120. *)
Lemma euclidean_block_split_list (R : realType) m n
    (x : inner_metric_space (@euclidean_inner_productP R (m+n))) :
  euclidean_coordinate_list x = euclidean_coordinate_list (euclidean_block_split x).1 ++
    euclidean_coordinate_list (euclidean_block_split x).2.
Proof.
have h := euclidean_block_join_list (@euclidean_block_split R m n x).
by rewrite euclidean_block_splitK in h.
Qed.

(** Source for [euclidean_dimension_cast]: supporting
    transport across equal arithmetic expressions for the
    dimension in Federer 2.6.5, p. 120. It changes
    only the proof-level dimension index. *)
Definition euclidean_dimension_cast (R : realType) n m (h : n = m)
    (x : inner_metric_space (@euclidean_inner_productP R n)) :
    inner_metric_space (@euclidean_inner_productP R m) :=
  match h with erefl => x end.
Arguments euclidean_dimension_cast {R n m} h x.

(** Source for [euclidean_dimension_castK]: supporting
    inverse dimension-index transport in the block identity
    of Federer 2.6.5, p. 120. *)
Lemma euclidean_dimension_castK (R : realType) n m (h : n = m) :
  cancel (@euclidean_dimension_cast R n m h) (euclidean_dimension_cast (esym h)).
Proof. destruct h; by []. Qed.

(** Source for [euclidean_dimension_cast_list]: supporting
    preservation of actual ordered coordinates by the
    dimension-index transport, Federer 2.6.5, p. 120. *)
Lemma euclidean_dimension_cast_list (R : realType) n m (h : n = m)
    (x : inner_metric_space (@euclidean_inner_productP R n)) :
  euclidean_coordinate_list (euclidean_dimension_cast h x) = euclidean_coordinate_list x.
Proof. destruct h; by []. Qed.

(** Source for [euclidean_join_coordinate_list]: supporting
    head-and-tail coordinate identification in the induction
    for Federer 2.6.5, p. 120. *)
Lemma euclidean_join_coordinate_list (R : realType) n
    (p : inner_metric_space (@euclidean_inner_productP R n) * R) :
  euclidean_coordinate_list (euclidean_join p) = p.2 :: euclidean_coordinate_list p.1.
Proof.
change (coordinate_head (euclidean_join p) ::
  euclidean_coordinate_list (coordinate_tail (euclidean_join p)) = p.2 :: euclidean_coordinate_list p.1).
have h := @euclidean_joinK R n p.
have ht := congr1 fst h; have hh := congr1 snd h.
by rewrite /euclidean_split /= in ht hh; rewrite ht hh.
Qed.
