(** Federer (1969), 2.2.6, p. 63, last paragraph: the countable Cartesian
    power of the positive-integer sequence space is homeomorphic with that
    space. All coordinate operations below use the public abstract
    realisation laws. Only general product topology and countable set theory
    are imported as background. Source context and encoding:
    SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceProductTopology
  SequenceCoordinateContinuity NaturalPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import ArrowAsProduct.

(** Source for [positive_sequence_flatten]: supporting reindexing
    map for Federer 2.2.6, p. 63: a single index selects an outer
    and an inner coordinate in a countable family of sequences. *)
Definition positive_sequence_flatten (R : realType) (decode : nat -> nat * nat)
    (f : nat -> positive_sequence_space R) : positive_sequence_space R :=
  positive_sequence_from_coordinates
    (fun k => positive_sequence_coordinates (f (decode k).1) (decode k).2).

(** Source for [positive_sequence_unflatten]: supporting inverse
    reindexing map for Federer 2.2.6, p. 63: a pair of indices
    selects a coordinate of the original sequence. *)
Definition positive_sequence_unflatten (R : realType) (encode : nat * nat -> nat)
    (x : positive_sequence_space R) : nat -> positive_sequence_space R :=
  fun i => positive_sequence_from_coordinates
    (fun j => positive_sequence_coordinates x (encode (i,j))).

(** Source for [positive_sequence_flattenK]: Federer 2.2.6,
    p. 63, supporting inverse law, using only the coordinate
    representation and the inverse laws of the index bijection. *)
Lemma positive_sequence_flattenK (R : realType) encode decode :
  cancel encode decode ->
  cancel (@positive_sequence_flatten R decode) (@positive_sequence_unflatten R encode).
Proof.
move=> h f; apply: funext=> i; apply: positive_sequence_extensionality=> j.
by rewrite /positive_sequence_unflatten /positive_sequence_flatten !positive_sequence_coordinatesK h.
Qed.

(** Source for [positive_sequence_unflattenK]: Federer 2.2.6,
    p. 63, supporting inverse law in the other direction for
    the countable-product homeomorphism. *)
Lemma positive_sequence_unflattenK (R : realType) encode decode :
  cancel decode encode ->
  cancel (@positive_sequence_unflatten R encode) (@positive_sequence_flatten R decode).
Proof.
move=> h x; apply: positive_sequence_extensionality=> k.
rewrite /positive_sequence_unflatten /positive_sequence_flatten !positive_sequence_coordinatesK.
by rewrite -surjective_pairing h.
Qed.

(** Source for [positive_sequence_flatten_continuous]: Federer 2.2.6, p. 63,
    continuity of the reindexing map from the Cartesian product: each output
    coordinate is one input coordinate. *)
Lemma positive_sequence_flatten_continuous (R : realType) decode :
  continuous (@positive_sequence_flatten R decode).
Proof.
apply/(proj2 (positive_sequence_coordinate_continuous _))=> f k.
have h : nbhs f [set g : nat -> positive_sequence_space R |
    positive_sequence_coordinates (g (decode k).1) (decode k).2 =
    positive_sequence_coordinates (f (decode k).1) (decode k).2].
  exact: (@proj_continuous _
    (fun _ : nat => [the topologicalType of positive_sequence_space R]) (decode k).1 f _
    (positive_sequence_coordinate_neighborhood (f (decode k).1) (decode k).2)).
apply: filterS h=> g hg.
by rewrite /= /positive_sequence_flatten !positive_sequence_coordinatesK.
Qed.

(** Source for [positive_sequence_unflatten_coordinate_continuous]:
    supporting continuity for Federer 2.2.6, p. 63: each factor
    of the inverse product map merely reindexes discrete coordinates. *)
Lemma positive_sequence_unflatten_coordinate_continuous (R : realType) encode i :
  continuous (fun x => @positive_sequence_unflatten R encode x i).
Proof.
apply/(proj2 (positive_sequence_coordinate_continuous _))=> x j.
apply: filterS (positive_sequence_coordinate_neighborhood x (encode (i,j)))=> y hy.
by rewrite /= /positive_sequence_unflatten !positive_sequence_coordinatesK.
Qed.

(** Source for [positive_sequence_unflatten_continuous]: Federer 2.2.6, p.
    63, continuity into the countable Cartesian product, obtained from
    continuity of every factor map. *)
Lemma positive_sequence_unflatten_continuous (R : realType) encode :
  continuous (@positive_sequence_unflatten R encode).
Proof.
move=> x; apply/cvg_sup; first exact/fmap_filter/nbhs_filter.
move=> i; move: x; apply/(@continuousP _ (initial_topology (@^~ i)))=> A [B hB <-].
apply: open_comp hB.
move=> y _; exact: positive_sequence_unflatten_coordinate_continuous.
Qed.

(** Source for [positive_sequence_countable_power_homeomorphism]: direct
    formalisation of Federer 2.2.6, p. 63, final assertion, as two
    continuous mutually inverse functions. The domain carries the Cartesian
    product topology. *)
Theorem positive_sequence_countable_power_homeomorphism (R : realType) :
  exists (f : (nat -> positive_sequence_space R) -> positive_sequence_space R)
         (g : positive_sequence_space R -> (nat -> positive_sequence_space R)),
    cancel f g /\ cancel g f /\ continuous f /\ continuous g.
Proof.
have [encode [decode [he hd]]] := natural_pairing_exists.
exists (@positive_sequence_flatten R decode), (@positive_sequence_unflatten R encode).
split; first exact: positive_sequence_flattenK he.
split; first exact: positive_sequence_unflattenK hd.
split; [exact: positive_sequence_flatten_continuous|exact: positive_sequence_unflatten_continuous].
Qed.
