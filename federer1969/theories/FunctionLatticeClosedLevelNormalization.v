(** Federer (1969), 2.5.3, p. 94: the unit-level form {h>=1} in the first
    and fourth further conditions. This supporting identity uses only the
    lattice's nonnegative scaling law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_lattice_closed_level_normalise]: Supporting Federer
    2.5.3, p. 94.The threshold is strictly positive. *)
Lemma positive_lattice_closed_level_normalise (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) (u : R) :
  positive_function_lattice L f -> 0 < u -> exists h : X -> R,
    positive_function_lattice L h /\ [set x | u <= f x]=[set x | 1 <= h x].
Proof.
move=> hf hu; exists (fun x => u^-1 * f x); split.
- apply: (@function_lattice_scale R X (positive_function_lattice L)
    (positive_function_lattice_laws hL) u^-1 f)=> //.
  by rewrite invr_ge0; exact: ltW hu.
- apply/seteqP; split=> x.
  + change (is_true (u <= f x) -> is_true (1 <= u^-1 * f x)).
    by rewrite (@ler_pdivlMl R u 1 (f x) hu) mulr1.
  + change (is_true (1 <= u^-1 * f x) -> is_true (u <= f x)).
    by rewrite (@ler_pdivlMl R u 1 (f x) hu) mulr1.
Qed.
