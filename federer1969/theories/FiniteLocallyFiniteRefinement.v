(** General topology supporting Federer (1969), 3.4.10,
    p. 337: finitely many pieces inside each
    member of a locally finite family form
    a locally finite family of actual subsets. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_locally_finite_refinement]: the
    finite local manifold covers in 3.4.10,
    p. 337, can be assembled over the
    locally finite ball refinement of 3.1.13,
    p. 225. This supporting topology statement
    uses only containment and finite local families. *)
Theorem finite_locally_finite_refinement (X:topologicalType) (J:choiceType)
    (U:set X) (I:set J) (K:J->set X) (P:J->set (set X)):
  is_locally_finite_family_on U I K ->
  (forall j,I j ->finite_set (P j)) ->
  (forall j,I j ->forall Q,P j Q ->Q `<=` K j) ->
  @is_locally_finite_family_on X [the choiceType of set X] U
    (\bigcup_(j in I) P j) (fun Q=>Q).
Proof.
move=>hLocal hFinite hContained x hx.
have [V [hV [hxV hHit]]]:=hLocal x hx.
pose D:set J:=I `&` [set j|exists y,V y /\K j y].
have hUnion:finite_set (\bigcup_(j in D) P j).
  apply:bigcup_finite;first exact:hHit.
  move=>j hj;exact:hFinite j hj.1.
exists V;split;first exact:hV.
split;first exact:hxV.
apply:(sub_finite_set _ hUnion)=>Q [[j hj hQ] [y [hyV hyQ]]].
exists j;last exact:hQ.
split;first exact:hj.
exists y;split;first exact:hyV.
exact:hContained j hj Q hQ y hyQ.
Qed.
