(** Parameter-to-center cardinal transfer for Federer (1969), 2.8.11, p.
    148. Projection identifies each part P_j with its centers B_j because
    the original family is controlled. Federer's original definition and
    strict controlledness are used here. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import DirectionalLimitationUP ControlledBallParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [directional_parameter_cardinal_bound]: the
    conclusion card P_j=card B_j<=zeta in Federer 2.8.11,
    p. 148. The center image lies in the required punctured
    neighborhood and satisfies the original radial separation
    condition. These explicit laws suffice to transfer the bound. *)
Lemma directional_parameter_cardinal_bound (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta tau : R) (zeta : nat)
    (P D : set (X*R)) (a : X) :
  is_directionally_limited_at A xi eta zeta ->
  is_controlled_ball_family tau P -> A a -> D `<=` P ->
  (forall p, D p -> ((A `&` metric_extended_open_ball a xi) `\` [set a]) p.1) ->
  (forall p q, D p -> D q -> p <> q -> forall x,
    is_radial_projection_configuration a p.1 q.1 x ->
    eta <= mdist x q.1 / mdist a q.1) -> D #<= [set: 'I_zeta].
Proof.
move=> hA hP ha hDP hcent hsep.
pose B : set X := (fun p : X*R => p.1) @` D.
have hB : B `<=` (A `&` metric_extended_open_ball a xi) `\` [set a].
  by move=> b [p hp <-]; exact: hcent p hp.
have hs : directionally_separated_from a eta B.
  move=> b c [p hp <-] [q hq <-] hne x hx.
  have hpq : p <> q by move=> he; apply: hne; rewrite he.
  exact: hsep p q hp hq hpq x hx.
have hbound := @directional_cardinal_bound R X A xi eta zeta hA a ha B hB hs.
have hinj : {in D &, injective (fun p : X*R => p.1)}.
  move=> p q hp hq he.
  exact (@controlled_centers_injective R X tau P hP p q
    (hDP p (set_mem hp)) (hDP q (set_mem hq)) he).
have heq := inj_card_eq hinj.
by rewrite (card_le_eql heq) in hbound.
Qed.
