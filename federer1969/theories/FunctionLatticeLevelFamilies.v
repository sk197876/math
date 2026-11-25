(** Federer (1969), 2.5.3, p. 94: the families F0, F1, and F2. Indices start
    at zero here, so the finite-measure first set is V 0. F2 depends on the
    measure; equality between representations must be proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [function_lattice_strict_levels]: direct F0 in Federer 2.5.3,
    p. 94, first paragraph The threshold is strictly positive. *)
Definition function_lattice_strict_levels (R : realType) (X : Type)
    (L : set (X -> R)) : set (set X) :=
  [set S | exists (f : X -> R) (t : R), positive_function_lattice L f /\
    (0 < t)%R /\ S = [set x | (t < f x)%R]].

(** Source for [function_lattice_increasing_levels]: direct F1 in Federer
    2.5.3, p. 94, first display of families The defining sequence is
    infinite even when its union is empty or finite. *)
Definition function_lattice_increasing_levels (R : realType) (X : Type)
    (L : set (X -> R)) : set (set X) :=
  [set S | exists V : nat -> set X,
    (forall n, function_lattice_strict_levels L (V n)) /\
    (forall n m, (n <= m)%N -> V n `<=` V m) /\
    S = \bigcup_(n in setT) V n].

(** Source for [function_lattice_finite_hulls]: direct F2 in Federer 2.5.3,
    p. 94, second display of families Finiteness of the first set is
    retained exactly, before taking the intersection. *)
Definition function_lattice_finite_hulls (R : realType) (X : Type)
    (L : set (X -> R)) (mu : set X -> \bar R) : set (set X) :=
  [set S | exists V : nat -> set X,
    (forall n, function_lattice_increasing_levels L (V n)) /\
    (forall n m, (n <= m)%N -> V m `<=` V n) /\
    mu (V 0%N) < +oo /\ S = \bigcap_(n in setT) V n].

(** Source for [function_lattice_strict_level_increasing]: constant-sequence
    inclusion F0 in F1 supporting Federer 2.5.3, p. 94 *)
Lemma function_lattice_strict_level_increasing (R : realType) (X : Type)
    (L : set (X -> R)) :
  function_lattice_strict_levels L `<=` function_lattice_increasing_levels L.
Proof.
move=> S hS; exists (fun _ => S); split; first by [].
split; first by move=> n m hnm x hx.
apply/seteqP; split=> x hx.
- by exists 0%N.
- by have [n _ hn] := hx.
Qed.

(** Source for [function_lattice_empty_strict_level]: the empty set is a
    positive strict level if L is nonempty; supporting Federer 2.5.3, p. 94 *)
Lemma function_lattice_empty_strict_level (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) :
  L f -> function_lattice_strict_levels L set0.
Proof.
move=> hf; exists (fun _ => 0%R), 1%R; split.
- split; first exact: (function_lattice_zero hL hf).
  by move=> x.
- split; first exact: ltr01.
  apply/seteqP; split=> x; first by [].
  by rewrite ltr10.
Qed.

(** Source for [empty_function_lattice_has_no_strict_levels]: boundary of F0
    in Federer 2.5.3, p. 94 *)
Lemma empty_function_lattice_has_no_strict_levels (R : realType) (X : Type) :
  function_lattice_strict_levels (set0 : set (X -> R)) = set0.
Proof.
apply/seteqP; split=> S; last by [].
by move=> [f [t [[hf _] _]]].
Qed.

(** Source for [empty_function_lattice_has_no_increasing_levels]: boundary
    of F1 in Federer 2.5.3, p. 94 *)
Lemma empty_function_lattice_has_no_increasing_levels (R : realType) (X : Type) :
  function_lattice_increasing_levels (set0 : set (X -> R)) = set0.
Proof.
apply/seteqP; split=> S; last by [].
move=> [V [hV _]]; have h := hV 0%N.
by rewrite empty_function_lattice_has_no_strict_levels in h.
Qed.

(** Source for [empty_function_lattice_has_no_finite_hulls]: supporting
    boundary of F2 in Federer 2.5.3, p. 94. No finite-measure hull exists
    for empty L. *)
Lemma empty_function_lattice_has_no_finite_hulls (R : realType) (X : Type)
    (mu : set X -> \bar R) :
  function_lattice_finite_hulls (set0 : set (X -> R)) mu = set0.
Proof.
apply/seteqP; split=> S; last by [].
move=> [V [hV _]]; have h := hV 0%N.
by rewrite empty_function_lattice_has_no_increasing_levels in h.
Qed.
