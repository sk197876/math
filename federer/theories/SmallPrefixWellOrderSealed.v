(** Sealed well-ordering representative supporting Federer (1969), 2.2.4, p.
    62 Only the representative and its small-prefix laws are exposed. Source
    editions: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import SmallPrefixWellOrderUP SmallPrefixWellOrderConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmallPrefixWellOrderSignature.
(** Source for [value]: abstract carrier/order pair supporting
    the well ordering in Federer 2.2.4, p. 62. *)
Parameter value : forall (J : choiceType) (D : set J), set J * rel J.
(** Source for [laws]: Supporting Federer 2.2.4, p. 62. *)
Parameter laws : forall (J : choiceType) (D : set J),
  is_small_prefix_well_order D (@value J D).1 (@value J D).2.
End SmallPrefixWellOrderSignature.
Module SmallPrefixWellOrder : SmallPrefixWellOrderSignature.
(** Source for [value]: private selection from the proved
    well-ordering existence for Federer 2.2.4, p. 62. *)
Definition value (J : choiceType) (D : set J) : set J * rel J :=
  let e := cid (@small_prefix_well_order_exists J D) in
  (projT1 e, projT1 (cid (projT2 e))).
(** Source for [laws]: the chosen representative discharges
    the abstract laws for Federer 2.2.4, p. 62. *)
Lemma laws (J : choiceType) (D : set J) :
  is_small_prefix_well_order D (@value J D).1 (@value J D).2.
Proof. exact: projT2 (cid (projT2 (cid (@small_prefix_well_order_exists J D)))). Qed.
End SmallPrefixWellOrder.
