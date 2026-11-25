(** Federer (1969), 4.1.1, pp. 344–345: convergence in the
    given function and weak dual topologies. The open-neighbourhood
    criterion is stated independently and connected to the
    general-topology interface. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_family_converges]: every open neighbourhood
    of the limit eventually holds, the topological meaning of
    convergence used in Federer 4.1.1, pp. 344–345. *)
Definition open_family_converges (X:Type) (O:set (set X))
    (F:set_system X) (x:X):=
  forall A,O A -> A x -> F A.

(** Source for [open_family_topological_convergence]: the raw
    open-neighbourhood criterion is equivalent to ordinary filter
    convergence, supporting Federer 4.1.1, pp. 344–345. *)
Theorem open_family_topological_convergence (X:topologicalType)
    (F:set_system X) (x:X):Filter F ->
  (open_family_converges (@open X) F x <-> F --> x).
Proof.
move=>hF; split.
- move=>hf A; rewrite nbhsE=> -[B [hB hBx] hBA].
  exact:filterS hBA (hf B hB hBx).
- move=>hf A hA hx; apply:hf; exact:open_nbhs_nbhs (conj hA hx).
Qed.
