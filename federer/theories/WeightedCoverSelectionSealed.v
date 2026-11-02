(** Opaque selected family for Federer (1969), 2.8.4, p. 143. Source context
    and the nonempty-member correction: WeightedCoverSelectionUP.v. Only the
    selection laws are exposed; the maximal-family implementation is
    private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import WeightedCoverSelectionUP WeightedCoverSelectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type WeightedCoverSelectionSignature.
(** Source for [value]: the disjointed selected family G
    of Federer 2.8.4, p. 143, specified by its laws. *)
Parameter value : forall (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R),
  (forall T, F T -> T <> set0) ->
  (forall T, F T -> 0 <= d T) ->
  (exists C, forall T, F T -> d T <= C) -> 1 < tau -> set (set X).
(** Source for [laws]: the intersection and weight comparison
    in Federer 2.8.4, p. 143, with its erratum's
    exclusion of empty eligible members. *)
Parameter laws : forall (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (he : forall T, F T -> T <> set0)
    (hn : forall T, F T -> 0 <= d T)
    (hb : exists C, forall T, F T -> d T <= C) (ht : 1 < tau),
  is_weighted_cover_selection F d tau (@value R X F d tau he hn hb ht).
End WeightedCoverSelectionSignature.

Module WeightedCoverSelection : WeightedCoverSelectionSignature.
(** Source for [value]: private selection of the family
    whose existence proves Federer 2.8.4, p. 143. *)
Definition value (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (he : forall T, F T -> T <> set0)
    (hn : forall T, F T -> 0 <= d T)
    (hb : exists C, forall T, F T -> d T <= C) (ht : 1 < tau) :=
  projT1 (cid (@weighted_cover_selection_exists R X F d tau he hn hb ht)).
(** Source for [laws]: the chosen family satisfies the
    abstract laws of Federer 2.8.4, p. 143. *)
Lemma laws (R : realType) (X : choiceType)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (he : forall T, F T -> T <> set0)
    (hn : forall T, F T -> 0 <= d T)
    (hb : exists C, forall T, F T -> d T <= C) (ht : 1 < tau) :
  is_weighted_cover_selection F d tau (@value R X F d tau he hn hb ht).
Proof. exact: projT2 (cid (@weighted_cover_selection_exists R X F d tau he hn hb ht)). Qed.
End WeightedCoverSelection.
