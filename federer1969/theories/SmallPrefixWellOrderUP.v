(** General set theory used in Federer (1969), 2.2.4, p. 62: choose a well
    ordering with small proper initial segments. We use an equipollent
    subset as the carrier, with an ambient well ordering, instead of
    constructing an initial ordinal. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [is_small_prefix_well_order]: Supporting Federer 2.2.4, p.
    62.C has the same cardinality as D and no proper initial segment has
    cardinality D. The relation is reflexive, with strictness expressed by
    inequality of its two elements. *)
Record is_small_prefix_well_order (J : choiceType) (D C : set J) (r : rel J) : Prop := {
  small_prefix_well_order_law : well_order r;
  small_prefix_representative_subset : C `<=` D;
  small_prefix_representative_cardinal : D #<= C;
  small_prefix_strict_cardinal : forall x, C x -> ~ (D #<= well_order_prefix C r x)
}.
