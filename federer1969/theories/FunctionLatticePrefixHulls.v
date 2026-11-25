(** Federer (1969), 2.5.3, pp. 94–95: decreasing level unions obtained by
    finite intersections. These supporting finite-intersection laws use
    indices starting at zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelFamilyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_sequence_prefix_intersection_step]: elementary
    finite-intersection identity supporting the decreasing hulls of Federer
    2.5.3, pp. 94–95 *)
Lemma set_sequence_prefix_intersection_step (X : Type) (V : nat -> set X) n :
  (\bigcap_(i in [set i | (i <= n.+1)%N]) V i)=
    (\bigcap_(i in [set i | (i <= n)%N]) V i) `&` V n.+1.
Proof.
apply/seteqP; split=> x.
- move=> hx; split.
  + move=> i hi; exact: hx i (leq_trans hi (leqnSn n)).
  + exact: hx n.+1 (leqnn n.+1).
- move=> [hx hn] i hi; case: (leqP i n)=> hin.
  + exact: hx i hin.
  + have he : i=n.+1 by apply/eqP; rewrite eqn_leq hi hin.
    by rewrite he.
Qed.

(** Source for [function_lattice_prefix_hull_member]: finite intersections
    remain in F1 in the hull proof of Federer 2.5.3, pp. 94–95 *)
Lemma function_lattice_prefix_hull_member (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (V : nat -> set X) :
  (forall n, function_lattice_increasing_levels L (V n)) ->
  forall n, function_lattice_increasing_levels L (\bigcap_(i in [set i | (i <= n)%N]) V i).
Proof.
move=> hV; elim=> [|n ih].
- have he : (\bigcap_(i in [set i | (i <= 0)%N]) V i)=V 0%N.
    apply/seteqP; split=> x hx.
    + exact: hx 0%N (leqnn 0%N).
    + move=> i hi; change (is_true ((i <= 0)%N)) in hi.
      have /eqP -> : i == 0%N by move: hi; rewrite leqn0.
      exact hx.
  rewrite he; exact: hV.
- rewrite set_sequence_prefix_intersection_step.
  exact: (function_lattice_increasing_levels_intersection hL ih (hV n.+1)).
Qed.
