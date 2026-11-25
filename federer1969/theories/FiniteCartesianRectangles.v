(** Federer (1969), 2.6.5, pp. 119–120: finite Cartesian products and
    Lebesgue products, using the rectangle equality of 2.6.2(2), p. 115. The
    present theorem gives arbitrary measurable rectangles, including
    infinite values, from the sealed finite-product laws. Stage n has n+1
    factors. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasure ProductRectangleValue
  FiniteCartesianMeasureUP FiniteCartesianMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cartesian_rectangle]: the finite Cartesian box
    underlying Federer 2.6.5, pp. 119–120 *)
Fixpoint finite_cartesian_rectangle (X : nat -> choiceType)
    (A : forall j, set (X j)) (n : nat) : set (finite_cartesian_carrier X n) :=
  match n as k return set (finite_cartesian_carrier X k) with
  | 0 => @A 0%N
  | k.+1 => @finite_cartesian_rectangle X A k `*` @A k.+1
  end.
Arguments finite_cartesian_rectangle {X} A n.

(** Source for [finite_cartesian_cost]: supporting finite
    product of factor measures in Federer 2.6.5,
    pp. 119–120, retaining the convention of 2.6.1,
    p. 115, that zero times infinity is zero. *)
Fixpoint finite_cartesian_cost (R : realType) (c : nat -> \bar R) (n : nat) : \bar R :=
  match n with
  | 0 => c 0%N
  | k.+1 => finite_cartesian_cost c k * c k.+1
  end.

(** Source for [finite_cartesian_rectangle_laws]: finite measurable-box
    formula supporting Federer 2.6.5, pp. 119–120, by repeated 2.6.2(2), p.
    115. Only factors actually present in the box need be measurable. *)
Theorem finite_cartesian_rectangle_laws (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j))
    (A : forall j, set (X j)) (n : nat) :
  (forall j, (j <= n)%N -> measure_measurable (@alpha j) (@A j)) ->
  measure_measurable (finite_cartesian_measure h_alpha n) (finite_cartesian_rectangle A n) /\
  finite_cartesian_measure h_alpha n (finite_cartesian_rectangle A n) =
    finite_cartesian_cost (fun j => @alpha j (@A j)) n.
Proof.
elim: n=> [|n ih] hA.
- rewrite finite_cartesian_measure_first /=; split=> //; exact: hA (leqnn 0).
- have hprev := ih (fun j hj => hA j (leq_trans hj (leqnSn n))).
  have hlast := hA n.+1 (leqnn _).
  rewrite finite_cartesian_measure_successor /=.
  have h := @product_measure_measurable_rectangle R (finite_cartesian_carrier X n) (X n.+1)
    (finite_cartesian_measure h_alpha n) (@alpha n.+1)
    (finite_cartesian_measure_is_measure h_alpha n) (h_alpha n.+1)
    (finite_cartesian_rectangle A n) (@A n.+1) hprev.1 hlast.
  split; first exact h.1.
  by rewrite h.2 hprev.2.
Qed.
