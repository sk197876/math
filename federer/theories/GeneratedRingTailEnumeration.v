(** Federer (1969), 3.4.8(8), p. 329:
    enumerate exactly the original remaining
    coordinate generators. Reuse the proved
    ordinal-tail enumeration and its completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP OrdinalCoordinateTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [generated_ring_tail_enumeration]: the
    original coordinates with indices at least
    m give a family of length n-m,
    supporting the original suffix-direction argument
    in 3.4.8(8), pp. 329–330. This
    changes only the generator indexing. *)
Theorem generated_ring_tail_enumeration (C:comNzRingType) n (x:'I_n->C)
  m (hMN:(m<=n)%N) (S:set C):
  is_generated_commutative_subring
    (fun y:C=>S y \/exists j:'I_n,(m<=j)%N /\y = x j) setT ->
  is_generated_commutative_subring
    (fun y:C=>(exists i:'I_(n-m),y = x (ordinal_coordinate_tail_index hMN i)) \/S y) setT.
Proof.
move=>hGenerated.
have hSets:(fun y:C=>S y \/exists j:'I_n,(m<=j)%N /\y = x j) =
    (fun y:C=>(exists i:'I_(n-m),y = x (ordinal_coordinate_tail_index hMN i)) \/S y).
  apply:funext=>y;apply:propext;split.
  - move=>[hS|[j [hJ hY]]];first by right.
    have [i hI]:=ordinal_coordinate_tail_complete hMN hJ.
    left;exists i;by rewrite hI.
  - move=>[[i hI]|hS];last by left.
    right;exists (ordinal_coordinate_tail_index hMN i);split;last exact:hI.
    by rewrite ordinal_coordinate_tail_value leq_addr.
by rewrite -hSets.
Qed.
