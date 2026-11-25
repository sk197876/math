(** Supporting distance existence for the project test of
    Federer 2.10.11, p. 176. Choice selects a witness of the
    independently stated first-difference laws; later use is sealed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import BinarySequenceCylinders BinaryPrefixDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [binary_prefix_distance_exists]: a concrete witness
    of the independent first-difference metric specification, supporting
    the project test of Federer 2.10.11, p. 176. This existence proof
    asserts no covering-measure or counterexample conclusion. *)
Lemma binary_prefix_distance_exists (R:realType) :
  exists d:binary_sequence_space->binary_sequence_space->R,
    is_binary_prefix_distance d.
Proof.
have hex x y:exists a:R,(x=y -> a= 0) /\
    (forall j,binary_first_difference x y j -> a=((2^j)%N)%:R^-1).
  case:(eqVneq x y)=> [he|hn].
  - exists 0;split=> // j [hj _].
    by rewrite he eqxx in hj.
  - have [i hi]:=binary_first_difference_exists hn.
    exists (((2^i)%N)%:R^-1);split.
    + move=> he;by rewrite he eqxx in hn.
    + move=> j hj;by rewrite (binary_first_difference_unique hi hj).
pose d x y:=projT1 (cid (hex x y)).
have hD x y:=projT2 (cid (hex x y)).
exists d;constructor.
- move=> x;exact:(hD x x).1 erefl.
- move=> x y j hj;exact:(hD x y).2 j hj.
Qed.
