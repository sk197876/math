(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CharacteristicFunctionUP WeightedCharacteristicExpansionUP GreedyCharacteristicSystemUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_system_precompose]: supporting compatibility of the
    inductive characteristic expansion with composition, Federer 2.4.18(1),
    proof p. 91 This supplies measurability of the pulled-back greedy sets
    by applying 2.3.3 to f composed with u, without assuming every
    measurable set pulls back. *)
Lemma greedy_system_precompose (R : realType) (X Y : Type)
    (u : X -> Y) (f : Y -> \bar R) (r : nat -> R)
    (A : nat -> set Y) (g : nat -> Y -> R) :
  is_greedy_characteristic_system f r A g ->
  is_greedy_characteristic_system (fun x => f (u x)) r
    (fun n => u @^-1` A n) (fun n x => g n (u x)).
Proof.
move=> hs; constructor.
- move=> n; constructor.
  + move=> x hx; exact: (characteristic_on_set (greedy_system_characteristic hs n) hx).
  + move=> x hx; exact: (characteristic_off_set (greedy_system_characteristic hs n) hx).
- move=> n x; exact: (greedy_system_threshold hs n (u x)).
Qed.
