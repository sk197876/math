(** Image of closed balls under reflection supporting Federer (1969),
    2.10.31, p. 196, the displayed equality rho_u B(a,epsilon)=
    B(y_j,epsilon). First prove the general isometry identity from the
    abstract reflection laws, then apply the sphere-chord calculation.
    Source context: NormalReflectionBoundary.v and SteinerChordReflection.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormalization UnitNormalGeometry
  NormalReflectionBoundary MetricClosedBalls SteinerChordReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_reflection_closed_ball_image]: supporting
    reflection of closed caps in the proof of
    2.10.31, p. 196. Every real radius is
    allowed, including zero and empty negative balls. *)
Lemma normal_reflection_closed_ball_image (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u : V)
    (a : inner_metric_space hB) (r : R) : B u u= 1 ->
  (normal_reflection hB u : inner_metric_space hB -> inner_metric_space hB) @` metric_closed_ball a r=
    metric_closed_ball (normal_reflection hB u a : inner_metric_space hB) r.
Proof.
move=> hu; apply/seteqP; split=> x.
- move=> [y hy <-].
  change (is_true (mdist (normal_reflection hB u a : inner_metric_space hB)
    (normal_reflection hB u y : inner_metric_space hB)<=r)).
  by rewrite (@normal_reflection_distance R V B hB u hu a y).
- move=> hx; exists (normal_reflection hB u x).
  + have he := @normal_reflection_distance R V B hB u hu (normal_reflection hB u a) x.
    rewrite (@normal_reflectionK R V B hB u hu a) in he.
    change (is_true (mdist a (normal_reflection hB u x : inner_metric_space hB)<=r)); by rewrite he.
  + exact (@normal_reflectionK R V B hB u hu x).
Qed.

(** Source for [unit_chord_reflection_closed_ball_image]: direct
    reflected-cap identity for distinct a,y_j
    on the sphere in 2.10.31, p. 196.
    The normal is precisely the normalised chord
    direction printed in the proof. *)
Theorem unit_chord_reflection_closed_ball_image (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (a y : inner_metric_space hB) (r : R) :
  a!=y -> inner_norm hB a=inner_norm hB y ->
  let u := inner_normalize hB (y-a) in
  (normal_reflection hB u : inner_metric_space hB -> inner_metric_space hB) @` metric_closed_ball a r=
    metric_closed_ball y r.
Proof.
move=> hay hnorm u.
have [hu hmove] := @unit_chord_reflection R V B hB a y hay hnorm.
by rewrite (@normal_reflection_closed_ball_image R V B hB u a r hu) hmove.
Qed.
