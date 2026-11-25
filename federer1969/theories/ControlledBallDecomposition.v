(** Federer (1969), Corollary 2.8.12, pp. 148–149: the closed balls of a
    controlled family with radii below mu<xi/2 form the union of 2 zeta+1
    disjointed subfamilies. Tau retains the conditions of 2.8.11, as
    inherited in the book. The proof follows repeated use of 2.8.10 and the
    cardinal contradiction of 2.8.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import DirectionalLimitationUP DirectionalCoverCardinality
  RadiusCoverSelectionUP RadiusSelectionIterationUP RadiusSelectionIterationLaws
  RadiusSelectionIteration BoundedRadiusIteration BallFamilyDecompositionUP
  BallFamilyDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [controlled_parameter_decomposition]: the
    separated parameter classes R_1,...,R_(2 zeta+1) covering Q
    in the proof of Federer 2.8.12, p. 149. The selected
    iteration is used only through its laws, and termination
    supplies coverage. No countability premise is imposed. *)
Theorem controlled_parameter_decomposition (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta tau mu : R) (zeta : nat)
    (Q : set (X*R)) :
  is_directionally_limited_at A xi eta zeta ->
  has_directional_cover_factor eta tau -> (0 < mu)%R ->
  is_controlled_ball_family tau Q -> (forall p, Q p -> A p.1) ->
  is_bounded_positive_radius_family mu Q ->
  (mu%:E < (1/2 : R)%:E * xi)%E ->
  exists C : 'I_(2*zeta+1) -> set (X*R), is_radius_parameter_decomposition Q C.
Proof.
move=> hlim hfactor hm hQ hA hbounded hsmall.
have ht := controlled_factor_gt_one hQ.
pose u := @radius_selection_iteration R X tau mu Q ht hm hbounded.
have hu : is_radius_selection_iteration tau Q u.1 u.2 :=
  radius_selection_iteration_specification ht hm hbounded.
have hfinal := @radius_selection_iteration_finishes R X A xi eta tau mu zeta Q u.1 u.2
  hlim hfactor hQ hA hbounded hsmall hu.
exists (fun i => u.2 i); constructor.
- move=> i p hp; exact (@radius_iteration_selected_subset R X tau Q u.1 u.2 hu i p hp).
- move=> i; exact (@radius_selection_separated R X tau (u.1 i) (u.2 i)
    (@radius_iteration_selection R X tau Q u.1 u.2 hu i)).
- apply/seteqP; split.
  + move=> p hp.
    have hn : ~ u.1 (2*zeta+1)%N p by rewrite hfinal.
    have [i [hi hs]] := @radius_iteration_selected_before R X tau Q u.1 u.2 hu
      (2*zeta+1)%N p hp hn.
    by exists (Ordinal hi).
  + move=> p [i _ hp]; exact: (@radius_iteration_selected_subset R X tau Q u.1 u.2 hu i p hp).
Qed.

(** Source for [federer_2_8_12]: the complete corollary in
    Federer 2.8.12, pp. 148–149. With the tau of 2.8.11
    and 0<mu<xi/2, the associated closed-ball family is the
    union of 2 zeta+1 disjointed subfamilies. The half-radius
    inequality uses positive real multiplication of xi, including
    infinity. Color classes may be empty or uncountable. *)
Theorem federer_2_8_12 (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta tau mu : R) (zeta : nat)
    (Q : set (X*R)) :
  is_directionally_limited_at A xi eta zeta ->
  has_directional_cover_factor eta tau -> (0 < mu)%R ->
  is_controlled_ball_family tau Q -> (forall p, Q p -> A p.1) ->
  is_bounded_positive_radius_family mu Q ->
  (mu%:E < (1/2 : R)%:E * xi)%E ->
  exists G : 'I_(2*zeta+1) -> set (set X),
    is_disjoint_ball_family_decomposition (associated_closed_ball_family Q) G.
Proof.
move=> hlim hfactor hm hQ hA hbounded hsmall.
have [C hC] := @controlled_parameter_decomposition R X A xi eta tau mu zeta Q
  hlim hfactor hm hQ hA hbounded hsmall.
exists (fun i => associated_closed_ball_family (C i)).
exact: parameter_decomposition_ball_families hC.
Qed.
