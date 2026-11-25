(** Federer (1969), 1.10.5, pp. 47-48: sealed existence
    of the suprema used in the norms. Source context and editions:
    ExtendedSupremumUP.v. Clients receive only the least-upper-bound
    laws; the bounded/unbounded witness is hidden by opaque ascription. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExtendedSupremumUP ExtendedSupremumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type ExtendedSupremumSignature.
(** Source for [value]: Federer 1.10.5, pp. 47-48,
    abstract supremum of a nonempty real value set, possibly infinite. *)
Parameter value : forall (R : realType) (S : set R), S !=set0 -> \bar R.
(** Source for [laws]: Federer 1.10.5, pp. 47-48,
    the supplied value obeys the proved least-upper-bound specification. *)
Parameter laws : forall (R : realType) (S : set R) (hn : S !=set0),
  is_extended_supremum S (@value R S hn).
End ExtendedSupremumSignature.

Module ExtendedSupremum : ExtendedSupremumSignature.
(** Source for [value]: Federer 1.10.5, pp. 47-48,
    private choice of the previously proved supremum witness. *)
Definition value (R : realType) (S : set R) (hn : S !=set0) :=
  projT1 (cid (@extended_supremum_exists R S hn)).
(** Source for [laws]: Federer 1.10.5, pp. 47-48,
    the chosen witness satisfies the specification, without new axioms. *)
Lemma laws (R : realType) (S : set R) (hn : S !=set0) :
  is_extended_supremum S (value hn).
Proof. exact: projT2 (cid (@extended_supremum_exists R S hn)). Qed.
End ExtendedSupremum.
