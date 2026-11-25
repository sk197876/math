(** Opaque shrinking-radius choice supporting Federer
    (1969), 3.2.16, p. 253, with the
    strict half-radius correction. Downstream proofs
    use the independent laws and not finite minima. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ShrinkingRadiusSelectionUP ShrinkingRadiusSelectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Module Type ShrinkingRadiusSelectionSignature.
(** Source for [value]: the selected delta_i of
    Federer 3.2.16, p. 253. Its hypotheses
    express proved availability and downward stability. *)
Parameter value : forall (R : realType) (P : nat -> R -> Prop),
  (forall n, exists r : R, 0<r /\ P n r) ->
  (forall n (r s : R), 0<s<=r -> P n r -> P n s) -> nat -> R.
(** Source for [laws]: positivity, the required
    small-ball property and strict half-radius
    decrease, Federer 3.2.16, p. 253;
    erratum p. 5, line 29. *)
Parameter laws : forall (R : realType) (P : nat -> R -> Prop)
  (hSmall : forall n, exists r : R, 0<r /\ P n r)
  (hDown : forall n (r s : R), 0<s<=r -> P n r -> P n s),
  is_shrinking_radius_selection P (@value R P hSmall hDown).
End ShrinkingRadiusSelectionSignature.
Module ShrinkingRadiusSelection : ShrinkingRadiusSelectionSignature.
(** Source for [value]: opaque selection from the
    proved radius existence for Federer 3.2.16,
    p. 253. *)
Definition value (R : realType) (P : nat -> R -> Prop)
  (hSmall : forall n, exists r : R, 0<r /\ P n r)
  (hDown : forall n (r s : R), 0<s<=r -> P n r -> P n s) :=
  projT1 (cid (@shrinking_radius_selection_exists R P hSmall hDown)).
(** Source for [laws]: the selected sequence has
    exactly the abstract shrinking-radius laws of
    Federer 3.2.16, p. 253, as corrected. *)
Lemma laws (R : realType) (P : nat -> R -> Prop)
  (hSmall : forall n, exists r : R, 0<r /\ P n r)
  (hDown : forall n (r s : R), 0<s<=r -> P n r -> P n s) :
  is_shrinking_radius_selection P (@value R P hSmall hDown).
Proof. exact: projT2 (cid (@shrinking_radius_selection_exists R P hSmall hDown)). Qed.
End ShrinkingRadiusSelection.
