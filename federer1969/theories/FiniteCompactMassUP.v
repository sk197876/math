(** Federer (1969), 2.10.48, p. 206: the supremum of the finite compact
    masses is approached by an increasing compact sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_compact_mass_values]: exactly the family
    in the displayed supremum of 2.10.48, p. 206, including
    the empty compact set and only finite masses. *)
Definition finite_compact_mass_values (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (S : set X) : set (\bar R) :=
  [set b | exists C, [/\ compact C, C `<=` S, mu C < +oo & b=mu C]].

(** Source for [is_finite_compact_mass_sequence]: abstract laws
    of the increasing sequence chosen in the proof of 2.10.48,
    p. 206. Its union dominates every finite compact mass. *)
Record is_finite_compact_mass_sequence (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (S : set X) (F : nat -> set X) : Prop := {
  (** Source for [finite_compact_sequence_members]: compactness,
      inclusion and finiteness in 2.10.48, p. 206. *)
  finite_compact_sequence_members : forall n,
    [/\ compact (F n), F n `<=` S & mu (F n)< +oo];
  (** Source for [finite_compact_sequence_increasing]: the nested
      choice of compact sets in 2.10.48, p. 206. *)
  finite_compact_sequence_increasing : forall n m, (n<=m)%N -> F n `<=` F m;
  (** Source for [finite_compact_sequence_cofinal]: the union attains
      the finite-compact supremum in 2.10.48, p. 206. *)
  finite_compact_sequence_cofinal : forall C, compact C -> C `<=` S ->
    mu C< +oo -> mu C<=mu (\bigcup_n F n)
}.
