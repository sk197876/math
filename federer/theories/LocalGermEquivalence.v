(** Federer (1969), 3.4.5, p. 319: the local-agreement
    relation is an equivalence, compatible with pointwise operations. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import LocalGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [locally_equal_refl]: reflexivity of the
    equivalence relation in 3.4.5, p. 319. *)
Lemma locally_equal_refl (X:topologicalType) (Y:Type) (a:X) (f:X->Y):
  locally_equal_at a f f.
Proof. exists setT;split;first exact:openT. by split. Qed.

(** Source for [locally_equal_sym]: symmetry of local
    agreement in 3.4.5, p. 319. *)
Lemma locally_equal_sym (X:topologicalType) (Y:Type) (a:X) (f g:X->Y):
  locally_equal_at a f g ->locally_equal_at a g f.
Proof.
move=>[U [hU [ha hEq]]];exists U;split;first exact:hU.
split;first exact:ha. by move=>x hx;symmetry;exact:hEq.
Qed.

(** Source for [locally_equal_trans]: transitivity of the
    equivalence in 3.4.5, p. 319, by intersecting the
    actual two open neighbourhoods. *)
Lemma locally_equal_trans (X:topologicalType) (Y:Type) (a:X) (f g h:X->Y):
  locally_equal_at a f g ->locally_equal_at a g h ->locally_equal_at a f h.
Proof.
move=>[U [hU [ha hEq]]] [V [hV [hb hEqV]]].
exists (U `&` V);split;first exact:openI hU hV.
split;first by split.
move=>x [hx hy];exact:eq_trans (hEq x hx) (hEqV x hy).
Qed.

(** Source for [locally_equal_unary]: compatibility with
    pointwise unary operations, used for ring negation and
    Boolean complement in 3.4.5, pp. 319–320. *)
Lemma locally_equal_unary (X:topologicalType) (Y Z:Type) (a:X)
    (op:Y->Z) (f g:X->Y):
  locally_equal_at a f g ->locally_equal_at a (fun x=>op (f x)) (fun x=>op (g x)).
Proof.
move=>[U [hU [ha hEq]]];exists U;split;first exact:hU.
split;first exact:ha. by move=>x hx;rewrite (hEq x hx).
Qed.

(** Source for [locally_equal_binary]: compatibility with
    pointwise addition, multiplication and Boolean operations
    in 3.4.5, pp. 319–320; use one common neighbourhood. *)
Lemma locally_equal_binary (X:topologicalType) (Y Z W:Type) (a:X)
    (op:Y->Z->W) (f f':X->Y) (g g':X->Z):
  locally_equal_at a f f' ->locally_equal_at a g g' ->
  locally_equal_at a (fun x=>op (f x) (g x)) (fun x=>op (f' x) (g' x)).
Proof.
move=>[U [hU [ha hF]]] [V [hV [hb hG]]].
exists (U `&` V);split;first exact:openI hU hV.
split;first by split.
by move=>x [hx hy];rewrite (hF x hx) (hG x hy).
Qed.

(** Source for [locally_equal_global]: globally equal
    representatives have the same germ, 3.4.5, p. 319. *)
Lemma locally_equal_global (X:topologicalType) (Y:Type) (a:X) (f g:X->Y):
  (forall x,f x=g x) ->locally_equal_at a f g.
Proof.
move=>hEq;exists setT;split;first exact:openT.
by split;[exact:Logic.I|move=>x _;exact:hEq].
Qed.
