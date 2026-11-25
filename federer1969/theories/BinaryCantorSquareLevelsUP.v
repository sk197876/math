(** Federer (1969), 3.3.20, p. 306:
    independent laws of the original Cartesian square levels. *)
From mathcomp Require Import all_boot finmap reals.
From Federer Require Import CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [is_binary_cantor_square_levels]: the
    original square levels consist exactly of pairs of
    original equal-level factor intervals, as in G_j
    of 3.3.20, p. 306. The Cartesian level
    identity is specified independently of any selected
    family. Counts, gaps, masses, projection properties
    and the square-refinement consequences are not laws. *)
Definition is_binary_cantor_square_levels (R:realType)
    (H:nat->{fset compact_real_intervals R})
    (G:nat->{fset (compact_real_intervals R*compact_real_intervals R)}):Prop:=
  forall j,G j=(H j `*` H j)%fset.

(** Source for [binary_cantor_square_levels_exist]: actual
    local square families with the independent Cartesian
    laws exist, 3.3.20, p. 306. This is
    only an existence witness; downstream proofs use
    the stated laws rather than a chosen construction. *)
Lemma binary_cantor_square_levels_exist (R:realType)
    (H:nat->{fset compact_real_intervals R}):
  exists G,is_binary_cantor_square_levels H G.
Proof. by exists (fun j=>(H j `*` H j)%fset). Qed.
