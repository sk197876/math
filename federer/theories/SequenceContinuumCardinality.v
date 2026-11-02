(** Set theory supporting Federer (1969), 2.2.4, p. 62: the sequence space
    has the cardinality of the power set of the naturals. We use the sealed
    sequence coordinates and the natural-pair bijection already established
    for 2.2.6. Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals.
From Federer Require Import SequenceSpace SequenceCoordinates NaturalPairing CardinalInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [positive_sequence_continuum_cardinality]: Supporting Federer
    2.2.4, p. 62.Binary coordinate codes inject subsets of naturals into N;
    graphs, indexed by a natural pairing, give the reverse bound. Zero and
    one here encode the positive values one and two. *)
Theorem positive_sequence_continuum_cardinality (R : realType) :
  (@setT (positive_sequence_space R)) #= (@setT (set nat)).
Proof.
apply/card_eqPle; split.
- have [encode [decode [he hd]]] := natural_pairing_exists.
  pose g (n : positive_sequence_space R) :=
    [set k | positive_sequence_coordinates n (decode k).1 = (decode k).2].
  have hi : injective g.
    move=> n m hnm; apply: positive_sequence_extensionality=> i.
    have hn : g n (encode (i,positive_sequence_coordinates n i)) by rewrite /g /= he.
    rewrite hnm /g /= he /= in hn; exact: esym hn.
  apply: (@cardinal_bound_of_injection _ _ setT setT g).
  + by move=> n _.
  + by move=> n m _ _; exact: hi.
- pose f (A : set nat) := @positive_sequence_from_coordinates R
    (fun i => if asbool (A i) then 0%N else 1%N).
  have hi : injective f.
    move=> A B hab; apply/seteqP; split=> i h.
    + apply: contrapT=> hn.
      have he := congr1 (fun n => positive_sequence_coordinates n i) hab.
      by rewrite /f !positive_sequence_coordinatesK (asboolT h) (asboolF hn) in he.
    + apply: contrapT=> hn.
      have he := congr1 (fun n => positive_sequence_coordinates n i) hab.
      by rewrite /f !positive_sequence_coordinatesK (asboolT h) (asboolF hn) in he.
  apply: (@cardinal_bound_of_injection _ _ setT setT f).
  + by move=> A _.
  + by move=> A B _ _; exact: hi.
Qed.
