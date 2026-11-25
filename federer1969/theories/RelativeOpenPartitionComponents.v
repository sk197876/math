(** Federer (1969), 3.4.8(10), p. 332:
    a disjoint relatively open partition
    preserves connected components. This general
    topology connection applies both to Y_nu
    and to the ordered sheets of Z. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_open_partition_components]:
    each component of Y outside delta=0
    is a component of some Y_nu,
    and each component of Z belongs
    to one ordered sheet, 3.4.8(10),
    p. 332. The argument uses
    relative openness, disjointness and exhaustiveness;
    the partition need not be finite. *)
Theorem relative_open_partition_components (X:topologicalType) (I:eqType)
    (A:set X) (S:I->set X):
  (forall i,relatively_open_set A (S i)) ->
  (forall x,A x ->exists i,S i x) ->
  (forall i j,i!=j ->forall x,S i x ->~S j x) ->
  forall i a,S i a ->connected_component A a = connected_component (S i) a.
Proof.
move=>hRelative hCover hDisjoint i a ha.
pose O:=fun j:I=>projT1 (cid (hRelative j)).
have hO j:open (O j) /\S j = A `&` O j:=projT2 (cid (hRelative j)).
have hSA j:S j `<=` A by move=>x;rewrite (hO j).2=>hx;exact:hx.1.
have hAa:A a:=hSA i a ha.
pose C:=connected_component A a.
pose U:set X:=\bigcup_(j in [set j:I|j!=i]) O j.
have hU:open U by apply:bigcup_open=>j _;exact:(hO j).1.
have hCSubset:C `<=` A:=@connected_component_sub X A a.
have hCa:C a:=connected_component_refl hAa.
have hComplement:C `&` O i = C `&` ~` U.
  apply/seteqP;split.
  - move=>x [hc ho];split;first exact:hc.
    move=>[j hJI hOj].
    have hSi:S i x by rewrite (hO i).2;split;[exact:hCSubset x hc|exact:ho].
    have hSj:S j x by rewrite (hO j).2;split;[exact:hCSubset x hc|exact:hOj].
    exact:hDisjoint j i hJI x hSj hSi.
  - move=>x [hc hNot];split;first exact:hc.
    have [j hj]:=hCover x (hCSubset x hc).
    case:(eqVneq j i)=>[hEqual|hDifferent].
    + rewrite -hEqual;rewrite (hO j).2 in hj;exact:hj.2.
    + exfalso;apply:hNot;exists j;first exact:hDifferent.
      rewrite (hO j).2 in hj;exact:hj.2.
have hWhole:C `&` O i = C.
  apply:(@component_connected X A a (C `&` O i)).
  - exists a;split;first exact:hCa.
    rewrite (hO i).2 in ha;exact:ha.2.
  - by exists (O i);first exact:(hO i).1.
  - exists (~` U);first exact:open_closedC hU.
    exact:hComplement.
have hInside:C `<=` S i.
  move=>x hx;have h:(C `&` O i) x by rewrite hWhole.
  by rewrite (hO i).2;split;[exact:hCSubset x hx|exact:h.2].
apply/seteqP;split.
- exact:(@connected_component_max X (S i) C a hCa hInside (@component_connected X A a)).
- apply:(@connected_component_max X A (connected_component (S i) a) a
    (connected_component_refl ha) _ (@component_connected X (S i) a)).
  move=>x hx;exact:hSA i x (@connected_component_sub X (S i) a x hx).
Qed.
