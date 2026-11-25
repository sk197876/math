(** Regression support for Federer (1969), 2.10.14, p. 177: changing a
    single curve value creates both one-sided jumps. This is a local example
    of the displayed upper-limit definitions, not a separately stated
    Federer lemma. the elementary upper-limit argument here needs no BV or
    target completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import CurveOneSidedJumpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [punctured_constant_curve_jump]: supporting isolated
    spike computation for the upper limits in 2.10.14, p. 177.
    Both oriented upper limits equal the distance between the
    exceptional value and the constant punctured-neighbourhood value. *)
Lemma punctured_constant_curve_jump (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) (c : Y) (right : bool) :
  (forall t, t<>x -> g t=c) ->
  curve_one_sided_jump g right x=(mdist c (g x))%:E.
Proof.
move=> hg.
have hne t : (0<curve_side_offset right x t)%R -> t<>x.
  move=> ht heq; move: ht; rewrite heq /curve_side_offset; by case: right; rewrite subrr ltxx.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: curve_one_sided_jump_upper_bound; exists 1%R; split; first exact: ltr01.
  by move=> t /andP[ht _]; rewrite (hg t (hne t ht)).
- apply: curve_one_sided_jump_lower_bound=> d hd.
  pose e : R := (d/2)%R.
  have he : (0<e)%R by rewrite /e divr_gt0 // ltr0n.
  have hed : (e<d)%R by rewrite /e; lra.
  pose t : R := if right then (x+e)%R else (x-e)%R.
  have ht : (0<curve_side_offset right x t<d)%R.
    by rewrite /t curve_side_offset_point he hed.
  exists t; split=> //; by rewrite (hg t (hne t (andP ht).1)).
Qed.
