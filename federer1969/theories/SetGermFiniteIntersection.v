(** Federer (1969), 3.4.8(13), p. 336:
    a finite nonempty intersection of representatives of
    one germ still represents that germ. Intersect their
    actual equality neighbourhoods; no compactness assertion
    about the germ space is used. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_finite_common_intersection]: the exact
    germ of the finite intersection S in the proof
    of 3.4.8(13), p. 336. The index
    family is explicitly nonempty. *)
Theorem set_germ_finite_common_intersection (X:topologicalType) a (J:finType)
    (j0:J) (F:J->set X) (H:set X):
  (forall j,@set_germ X a (F j)=@set_germ X a H) ->
  @set_germ X a (\bigcap_j F j)=@set_germ X a H.
Proof.
move=>hGerm.
have hEach j:exists U:set X,open U /\U a /\F j `&` U=H `&` U.
  exact:(@set_germ_equality_original X a (F j) H).1 (hGerm j).
have [U hU]:=choice hEach.
pose W:set X:=~` (\bigcup_j (~` U j)).
have hClosed:closed (\bigcup_j (~` U j)).
  apply:(closed_bigcup (@finite_finset J setT))=>j _.
  exact:open_closedC (hU j).1.
have hW:open W:=closed_openC hClosed.
have hWMember x:W x <->forall j,U j x.
  split.
  - move=>hx j;apply:contrapT=>hNot;apply:hx;by exists j.
  - move=>hx [j _ hNot];exact:hNot (hx j).
apply/set_germ_equality_original;exists W;split;first exact:hW.
split;first by apply/hWMember=>j;exact:(hU j).2.1.
apply/seteqP;split.
- move=>x [hx hWx];split;last exact:hWx.
  have hMember:(H `&` U j0) x by rewrite -(hU j0).2.2;split;[exact:hx j0 Logic.I|exact:(hWMember x).1 hWx j0].
  exact:hMember.1.
- move=>x [hx hWx];split;last exact:hWx.
  move=>j _.
  have hMember:(F j `&` U j) x by rewrite (hU j).2.2;split;[exact:hx|exact:(hWMember x).1 hWx j].
  exact:hMember.1.
Qed.
