(** Private existence witness for the compact-test supremum in Federer
    (1969), 2.5.14, p. 107. Source context and correction locator:
    CompactOpenContentUP.v. The only ingredient is the project's sealed
    extended supremum. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import CompactOpenContentUP ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_content_exists]: supporting existence of the
    supremum alpha(V) in Federer 2.5.14, p. 107 No positivity hypothesis is
    needed for existence of an extended supremum. *)
Lemma compact_open_content_exists (R : realType) (X : topologicalType) (A : (X -> R) -> R) :
  exists a, is_compact_open_content A a.
Proof.
exists (fun V => extended_real_sup [set c | exists f, is_compact_open_test_function V f /\ c=(A f)%:E]).
move=> V _; constructor; [exact: extended_real_sup_upper|exact: extended_real_sup_least].
Qed.
