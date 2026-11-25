(** Corrected Federer (1969), 2.10.17(2), p. 179. Use the same
    regular-measure, B-set exhaustion and strict upper-density proof, with
    the zero-denominator correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RegularMeasureUP CaratheodoryLimitUP
  CaratheodoryDensityFunction CaratheodoryDensityLocalBound CoveringRelationUP CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_family_relation]: direct relation
    C={(x,S):x in S in F} in 2.10.17, p. 179.
    The family is a set of sets, so costs are extensional. *)
Definition caratheodory_family_relation (X : Type) (F : set (set X)) (x : X) (S : set X) :=
  F S /\ S x.

(** Source for [caratheodory_density_upper_bound]: supporting strict-density
    estimate for corrected 2.10.17(2), p. 179 Fineness and the lower bound
    zero are unnecessary for this implication once the corrected upper limit
    gives the quantitative local generator estimate. *)
Theorem caratheodory_density_upper_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (mu psi : set X -> \bar R)
    (A : set X) (t : R) :
  is_measure mu -> is_regular_measure mu -> (forall S, F S -> 0<=c S) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (0<t)%R ->
  (forall x, A x -> covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_density_function mu c A) x<t%:E) ->
  mu A<=t%:E*psi A.
Proof.
move=> hm hr hc hpsi ht hbound.
apply: (@caratheodory_density_local_bound R X [the choiceType of set_type F]
  (fun j => val j) (fun j => c (val j)) mu psi A t hm hr _ hpsi ht).
- by move=> j; apply: hc; exact: set_valP.
- move=> x hx.
  have hcost S : caratheodory_family_relation F x S -> 0<=c S.
    by move=> [hF _]; exact: hc.
  have [delta [hd hgen]] := @caratheodory_density_upper_local_estimate R X mu hm c
    (caratheodory_family_relation F) A x t ht hcost (hbound x hx).
  exists delta; split=> // j hj hdiam.
  apply: hgen _ _ hdiam; split=> //; exact: set_valP.
Qed.

(** Source for [federer_2_10_17_2]: corrected direct statement of
    2.10.17(2), p. 179, retaining the standing fineness and the printed
    0<=upper density<t. *)
Theorem federer_2_10_17_2 (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (mu psi : set X -> \bar R)
    (A : set X) (t : R) :
  is_measure mu -> is_regular_measure mu -> (forall S, F S -> 0<=c S) ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (0<t)%R ->
  (forall x, A x -> 0<=covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_density_function mu c A) x /\
    covering_upper_limit (caratheodory_family_relation F) (caratheodory_density_function mu c A) x<t%:E) ->
  mu A<=t%:E*psi A.
Proof.
move=> hm hr hc hf hpsi ht hbound.
apply: caratheodory_density_upper_bound hm hr hc hpsi ht _=> x hx.
exact: (hbound x hx).2.
Qed.
