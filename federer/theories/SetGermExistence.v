(** Federer (1969), 3.4.5, pp. 319–320: neighbourhood
    equivalence is exactly equality of set germs, and Boolean
    operations descend to the opaque germ space. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import LocalGermUP LocalGermEquivalence LocalGermSealed LocalGermLift SetGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_equality_original]: two sets have the
    same germ precisely when their intersections with some actual
    neighbourhood agree, 3.4.5, p. 319. *)
Theorem set_germ_equality_original (X:topologicalType) (a:X) (S T:set X):
  set_germ a S=set_germ a T <->
  exists U:set X,open U /\ U a /\ S `&` U=T `&` U.
Proof.
have hG:=@LocalGerms.laws X Prop [the choiceType of set X] (fun S=>S) a.
rewrite /set_germ (local_germ_equality hG);split.
- move=>[U [hU [ha hEq]]];exists U;split;first exact:hU.
  split;first exact:ha.
  apply/seteqP;split.
  + move=>x [hx hu];split;last exact:hu.
    by rewrite -(hEq x hu).
  + move=>x [hx hu];split;last exact:hu.
    by rewrite (hEq x hu).
- move=>[U [hU [ha hEq]]];exists U;split;first exact:hU.
  split;first exact:ha.
  move=>x hx;apply:propext;split=>h.
  + have hMember:(T `&` U) x by rewrite -hEq;split.
    exact:hMember.1.
  + have hMember:(S `&` U) x by rewrite hEq;split.
    exact:hMember.1.
Qed.

(** Source for [set_germ_operations_exists]: the Boolean
    operations asserted in 3.4.5, pp. 319–320, exist
    because each pointwise operation preserves local agreement. *)
Theorem set_germ_operations_exists (X:topologicalType) (a:X):
  exists (join meet:set_germ_space a->set_germ_space a->set_germ_space a)
    (neg:set_germ_space a->set_germ_space a),is_set_germ_operations join meet neg.
Proof.
have hG:=@LocalGerms.laws X Prop [the choiceType of set X] (fun S=>S) a.
have hUnion (S S' T T':set X):
    locally_equal_at a S S' ->locally_equal_at a T T' ->
    locally_equal_at a (S `|` T) (S' `|` T').
  exact:(@locally_equal_binary X Prop Prop Prop a or S S' T T').
have hInter (S S' T T':set X):
    locally_equal_at a S S' ->locally_equal_at a T T' ->
    locally_equal_at a (S `&` T) (S' `&` T').
  exact:(@locally_equal_binary X Prop Prop Prop a and S S' T T').
have hNeg (S T:set X):locally_equal_at a S T ->locally_equal_at a (~` S) (~` T).
  exact:(@locally_equal_unary X Prop Prop a not S T).
have [join hJoin]:=@local_germ_binary_lift_exists X Prop [the choiceType of set X]
  (fun S=>S) a (set_germ_space a) (@set_germ X a) hG (fun S T=>S `|` T) hUnion.
have [meet hMeet]:=@local_germ_binary_lift_exists X Prop [the choiceType of set X]
  (fun S=>S) a (set_germ_space a) (@set_germ X a) hG (fun S T=>S `&` T) hInter.
have [neg hNegation]:=@local_germ_unary_lift_exists X Prop [the choiceType of set X]
  (fun S=>S) a (set_germ_space a) (@set_germ X a) hG (fun S=>~` S) hNeg.
exists join,meet,neg;by constructor.
Qed.
