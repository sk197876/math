(** Federer (1969), proof of 2.5.2, p. 93: the truncated layers lie below
    the limiting tail and below f. These scalar comparisons support passage
    to the two increasing limits without assuming in advance that f is
    summable. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLayers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_lattice_layer_below_tail]: each finite layer is below
    f-f_a in the first limit of Federer 2.5.2, p. 93 *)
Lemma real_lattice_layer_below_tail (R : realType) (X : Type) (f : X -> R) a b :
  function_le (real_lattice_layer f a b) (real_lattice_tail f a).
Proof. by move=> x; rewrite /real_lattice_layer /real_lattice_tail lerD2r ge_min lexx. Qed.

(** Source for [real_lattice_tail_below_function]: the tail f-f_a is bounded
    above by f for f >= 0 and a >= 0, supporting the limiting inequalities
    in Federer 2.5.2, p. 93 *)
Lemma real_lattice_tail_below_function (R : realType) (X : Type) (f : X -> R) a :
  function_nonnegative f -> 0 <= a -> function_le (real_lattice_tail f a) f.
Proof.
move=> hf ha x; by rewrite /real_lattice_tail lerBlDr lerDl le_min (hf x) ha.
Qed.

(** Source for [real_lattice_layer_below_function]: the finite middle layer
    is bounded by f in Federer 2.5.2, p. 93 *)
Lemma real_lattice_layer_below_function (R : realType) (X : Type) (f : X -> R) a b :
  function_nonnegative f -> 0 <= a -> function_le (real_lattice_layer f a b) f.
Proof.
move=> hf ha x; exact: le_trans (real_lattice_layer_below_tail f a b x)
  (real_lattice_tail_below_function hf ha x).
Qed.
