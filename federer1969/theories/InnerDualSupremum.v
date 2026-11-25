(** Federer (1969), 1.7.2, pp. 28-29: the printed supremum formula. The
    supremum is evaluated from the locally proved upper bound and its
    attainment, not from an external theorem about dual norms. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals.
From Federer Require Import InnerProductUP InnerNorm OneFormLinear Hom
  LinearBasis AlternatingCoordinates.
From Federer Require Import InnerDual InnerDualNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DualSupremum.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation F := (A_m V R^o 1).

(** Source for [inner_dual_unit_values]: Federer 1.7.2, p. 28,
    the set of evaluations of a covector on the primal unit ball. *)
Definition inner_dual_unit_values (a : F) : set R :=
  [set r | exists x, inner_norm hB x <= 1 /\ r = one_hom a x].

(** Source for [inner_dual_norm_supremum]: Federer 1.7.2,
    pp. 28-29, displayed formula: the norm of alpha is the supremum
    of its evaluations on vectors with norm at most one. *)
Theorem inner_dual_norm_supremum (a : F) :
  inner_dual_norm hB he a = sup (inner_dual_unit_values a).
Proof.
pose D := inner_dual_norm hB he a.
have hu : ubound (inner_dual_unit_values a) D.
  move=> r [x [hx ->]]; exact: inner_dual_unit_bound.
have [x [hx ha]] := inner_dual_norm_attained hB he a.
have hD : inner_dual_unit_values a D by exists x; split=> //; exact: esym ha.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: ub_le_sup hD; by exists D.
- apply: ge_sup hu; by exists D.
Qed.
End DualSupremum.
