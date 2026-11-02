(** Federer (1969), 2.5.3, pp. 94–95: closure properties of the level
    families used to form regular hulls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeLevelFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [function_lattice_strict_level_normalise]: scaling a positive
    threshold to one, supporting F0 in Federer 2.5.3, p. 94 *)
Lemma function_lattice_strict_level_normalise (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (S : set X) :
  function_lattice_strict_levels L S -> exists f : X -> R,
    positive_function_lattice L f /\ S=[set x | 1 < f x].
Proof.
move=> [f [t [hf [ht ->]]]]; exists (fun x => t^-1 * f x); split.
- apply: (@function_lattice_scale R X (positive_function_lattice L)
    (positive_function_lattice_laws hL) t^-1 f)=> //.
  by rewrite invr_ge0; exact: ltW ht.
- apply/seteqP; split=> x.
  + change (is_true (t < f x) -> is_true (1 < t^-1 * f x)).
    by rewrite (@ltr_pdivlMl R t 1 (f x) ht) mulr1.
  + change (is_true (1 < t^-1 * f x) -> is_true (t < f x)).
    by rewrite (@ltr_pdivlMl R t 1 (f x) ht) mulr1.
Qed.

(** Source for [function_lattice_strict_levels_union]: F0 is closed under
    binary union; supporting Federer 2.5.3, p. 94 *)
Lemma function_lattice_strict_levels_union (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (S T : set X) :
  function_lattice_strict_levels L S -> function_lattice_strict_levels L T ->
  function_lattice_strict_levels L (S `|` T).
Proof.
move=> hS hT.
have [f [hf ->]] := function_lattice_strict_level_normalise hL hS.
have [g [hg ->]] := function_lattice_strict_level_normalise hL hT.
exists (fun x => Order.max (f x) (g x)),1; split.
- exact: (@function_lattice_maximum R X (positive_function_lattice L)
    (positive_function_lattice_laws hL) f g hf hg).
- split; first exact: ltr01.
  apply/seteqP; split=> x.
  + move=> [hx|hx]; change (is_true (1 < Order.max (f x) (g x)));
      rewrite lt_max; apply/orP; [left|right]; exact hx.
  + move=> hx; change (is_true (1 < Order.max (f x) (g x))) in hx.
    move: hx; rewrite lt_max; move/orP=> [hx|hx]; [left|right]; exact hx.
Qed.

(** Source for [function_lattice_strict_levels_intersection]: F0 is closed
    under binary intersection; supporting Federer 2.5.3, p. 94 *)
Lemma function_lattice_strict_levels_intersection (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (S T : set X) :
  function_lattice_strict_levels L S -> function_lattice_strict_levels L T ->
  function_lattice_strict_levels L (S `&` T).
Proof.
move=> hS hT.
have [f [hf ->]] := function_lattice_strict_level_normalise hL hS.
have [g [hg ->]] := function_lattice_strict_level_normalise hL hT.
exists (fun x => Order.min (f x) (g x)),1; split.
- exact: (@function_lattice_minimum R X (positive_function_lattice L)
    (positive_function_lattice_laws hL) f g hf hg).
- split; first exact: ltr01.
  apply/seteqP; split=> x.
  + move=> [hx hy]; change (is_true (1 < Order.min (f x) (g x))); by rewrite lt_min hx hy.
  + move=> hx; change (is_true (1 < Order.min (f x) (g x))) in hx.
    move: hx; rewrite lt_min; move/andP=> [hx hy]; by split.
Qed.

(** Source for [function_lattice_increasing_levels_intersection]: closure of
    F1 under binary intersection, supporting the decreasing hulls in Federer
    2.5.3, pp. 94–95 The diagonal intersections suffice because the defining
    sequences increase. *)
Lemma function_lattice_increasing_levels_intersection (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (S T : set X) :
  function_lattice_increasing_levels L S -> function_lattice_increasing_levels L T ->
  function_lattice_increasing_levels L (S `&` T).
Proof.
move=> [V [hV [hVi ->]]] [W [hW [hWi ->]]].
exists (fun n => V n `&` W n); split.
- move=> n; exact: (function_lattice_strict_levels_intersection hL (hV n) (hW n)).
- split.
  + move=> n m hnm x [hx hy]; split; [exact: hVi n m hnm x hx|exact: hWi n m hnm x hy].
  + apply/seteqP; split=> x.
    * move=> [[n _ hn] [m _ hm]]; exists (maxn n m)=> //; split.
      -- exact: hVi n (maxn n m) (leq_maxl n m) x hn.
      -- exact: hWi m (maxn n m) (leq_maxr n m) x hm.
    * move=> [n _ [hn hm]]; split; by exists n.
Qed.
