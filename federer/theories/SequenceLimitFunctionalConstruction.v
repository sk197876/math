(** Private existence witness for the limit functional in Federer (1969),
    2.5.3, p. 95 Choice selects the already unique finite limit on the
    lattice; off-lattice values are irrelevant. Downstream results use only
    SequenceLimitFunctionalUP.v through the opaque seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ConvergentSequenceLattice SequenceLimitFunctionalUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_limit_functional_exists]: existence of the map
    defined in Federer 2.5.3, p. 95 *)
Theorem sequence_limit_functional_exists (R : realType) :
  exists A : (nat -> R) -> R, is_sequence_limit_functional A.
Proof.
have happ f : exists a : R, convergent_real_sequences f ->
    extended_order_limit (fun n => (f n)%:E) a%:E.
  case: (pselect (convergent_real_sequences f))=> hf.
  - have [a ha] := hf; by exists a.
  - by exists 0%R.
exists (fun f => projT1 (cid (happ f)))=> f hf.
exact: (projT2 (cid (happ f)) hf).
Qed.
