(** Federer (1969), 4.1.1, pp. 344–345: elementary open-set
    consequences supporting continuity and final-topology comparisons.
    These are general-topology connections, not additional book claims. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_family_empty]: the empty set is open,
    supporting the topologies in Federer 4.1.1, p. 344. *)
Lemma open_family_empty (X:Type) (O:set (set X)) :
  is_open_family_topology O -> O set0.
Proof.
move=>hO.
have h:O (\bigcup_(i:False) (set0:set X)).
  apply:(open_family_union hO)=>i; exact:False_ind _ i.
have he:(\bigcup_(i:False) (set0:set X))=set0.
  apply:funext=>x; apply:propext; split.
  - by move=>[i _ hi].
  - by move=>hx.
by rewrite he in h.
Qed.

(** Source for [open_family_locally_open]: a set is open exactly
    when it is a neighbourhood of each of its points, supporting
    the basic neighbourhoods in Federer 4.1.1, p. 344. *)
Theorem open_family_locally_open (X:Type) (O:set (set X)) (A:set X) :
  is_open_family_topology O ->
  (O A <-> forall x,A x -> open_family_neighbourhood O x A).
Proof.
move=>hO; split.
- by move=>hA x hx; exists A; split=>//; split=>// y hy.
- move=>hA.
  pose J:={B:set X|O B /\ B `<=` A}.
  pose V(j:J):set X:=proj1_sig j.
  have hV:O (\bigcup_j V j).
    apply:(open_family_union hO)=>j; exact:(proj2_sig j).1.
  have he:A=(\bigcup_j V j).
    apply:funext=>x; apply:propext; split.
    + move=>hx; have [B [hB [hBx hBA]]]:=hA x hx.
      by exists (exist _ B (conj hB hBA)).
    + move=>[j _ hj]; exact:(proj2_sig j).2 x hj.
  by rewrite -he in hV.
Qed.
