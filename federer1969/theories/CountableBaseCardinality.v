(** Federer (1969), 2.2.4, p. 62: the family of closed subsets has
    cardinality at most continuum in a space with a countable base. We
    encode an open set by the indices of all basic sets it contains, an
    injective form of the same union argument. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP CardinalInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [open_base_index_code]: Supporting Federer 2.2.4, p. 62. *)
Definition open_base_index_code (T : topologicalType) (U : nat -> set T)
    (V : set T) : set nat := [set i | U i `<=` V].

(** Source for [open_base_index_code_injective]: Supporting Federer 2.2.4,
    p. 62.Equal index codes give the same union of basic neighborhoods and
    hence the same open set. *)
Lemma open_base_index_code_injective (T : topologicalType) (U : nat -> set T) :
  is_countable_open_base U -> forall A B, open A -> open B ->
  open_base_index_code U A = open_base_index_code U B -> A = B.
Proof.
move=> hU A B hA hB he; apply/seteqP; split=> x hx.
- have [i [hi his]] := @countable_base_refines T U hU A hA x hx.
  have hh : open_base_index_code U A i := his.
  rewrite he in hh; exact: hh x hi.
- have [i [hi his]] := @countable_base_refines T U hU B hB x hx.
  have hh : open_base_index_code U B i := his.
  rewrite -he in hh; exact: hh x hi.
Qed.

(** Source for [countable_base_open_cardinality_bound]: Supporting Federer
    2.2.4, p. 62. *)
Lemma countable_base_open_cardinality_bound (T : topologicalType) (U : nat -> set T) :
  is_countable_open_base U -> (@open T) #<= (@setT (set nat)).
Proof.
move=> hU; apply: (@cardinal_bound_of_injection _ _ (@open T) setT (open_base_index_code U)).
- by move=> A _.
- move=> A B hA hB he; apply: (@open_base_index_code_injective T U hU A B _ _ he).
  + exact: set_mem hA.
  + exact: set_mem hB.
Qed.

(** Source for [countable_base_closed_cardinality_bound]: direct cardinal
    bound used for the family Gamma in Federer 2.2.4, p. 62, derived.
    Complementation injects closed sets into the topology. *)
Lemma countable_base_closed_cardinality_bound (T : topologicalType) (U : nat -> set T) :
  is_countable_open_base U -> (@closed T) #<= (@setT (set nat)).
Proof.
move=> hU; apply: card_le_trans _ (countable_base_open_cardinality_bound hU).
apply: (@cardinal_bound_of_injection _ _ (@closed T) (@open T) (fun A => ~` A)).
- move=> A hA; exact: closed_openC hA.
- move=> A B _ _ he; have hh := congr1 (fun C : set T => ~` C) he.
  by rewrite !setCK in hh.
Qed.
