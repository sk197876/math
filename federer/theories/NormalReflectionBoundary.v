(** Reflection and closed-ball boundary invariance supporting Federer
    (1969), 2.10.30, p. 195. Derive the metric isometry and continuity from
    the proved orthogonal reflection laws. A continuous involution
    preserving the ball also preserves its interior, hence its actual
    topological boundary. Source context: UnitNormalGeometry.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Bilinear InnerProductUP InnerNorm InnerMetric OrthonormalFamilies OrthogonalMaps
  UnitNormalGeometry NormMetricScaleContinuity MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Reflection.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation E := (inner_metric_space hB).
Variable u : V.
Hypothesis hu : B u u= 1.
Local Notation f := (normal_reflection hB u).

(** Source for [normal_reflection_norm]: supporting
    norm preservation of rho_u in O(n) for
    2.10.30, p. 195, from its proved
    orthogonality law. *)
Lemma normal_reflection_norm x : inner_norm hB (f x)=inner_norm hB x.
Proof.
exact (@orthogonal_map_norm R V V B B hB hB
  (GRing.Linear.clone _ _ _ _ f _) (@normal_reflection_orthogonal R V B hB u hu) x).
Qed.

(** Source for [normal_reflection_distance]: supporting
    metric isometry of the reflection in 2.10.30,
    p. 195. *)
Lemma normal_reflection_distance (x y : E) : mdist (f x : E) (f y : E)=mdist x y.
Proof.
have he : f (x-y)=f x-f y := linB (@normal_reflection_linear R V B hB u) x y.
rewrite !inner_metric_distanceE -he; exact: normal_reflection_norm.
Qed.

(** Source for [normal_reflection_continuous]: supporting
    continuity for reflection of the containing-ball
    boundary in 2.10.30, p. 195. *)
Lemma normal_reflection_continuous : continuous (f : E -> E).
Proof.
apply: (@metric_fixed_lipschitz_continuous R E E f 1 (@ler01 R))=> x y.
by rewrite normal_reflection_distance mul1r.
Qed.

(** Source for [normal_reflection_ball_preimage]: supporting
    reflection invariance of the containing closed
    ball in 2.10.30, p. 195, including
    radius zero and empty negative-radius balls. *)
Lemma normal_reflection_ball_preimage r : (f : E -> E) @^-1` metric_closed_ball (0 : E) r=
  metric_closed_ball (0 : E) r.
Proof.
by apply/seteqP; split=> x;
  rewrite /metric_closed_ball /= !inner_metric_distanceE !sub0r !inner_normN normal_reflection_norm.
Qed.

(** Source for [normal_reflection_ball_boundary]: supporting
    invariance of Z=Bdry B(0,r) in the
    final inclusion of 2.10.30, p. 195.
    The boundary is closure minus interior, rather
    than an assumed equality with a distance sphere. *)
Lemma normal_reflection_ball_boundary r (x : E) :
  let C := metric_closed_ball (0 : E) r in
  (closure C `\` interior C) (f x) <-> (closure C `\` interior C) x.
Proof.
move=> C.
have he : closure C=C := esym ((closure_id C).1 (@metric_closed_ball_closed R E (0 : E) r)).
have hpre : (f : E -> E) @^-1` C=C := normal_reflection_ball_preimage r.
have hi (z : E) : interior C (f z) -> interior C z.
  move=> hz; have hn := @normal_reflection_continuous z C hz.
  change (nbhs z ((f : E -> E) @^-1` C)) in hn.
  by rewrite hpre in hn.
rewrite he; split; move=> [hx hi0]; split.
- have hh : ((f : E -> E) @^-1` C) x := hx; by rewrite hpre in hh.
- move=> hxI; apply: hi0.
  have hh := hi (f x); rewrite (@normal_reflectionK R V B hB u hu x) in hh.
  exact: hh hxI.
- have hh : ((f : E -> E) @^-1` C) x by rewrite hpre.
  exact hh.
- move=> hxI; exact: hi0 (hi x hxI).
Qed.
End Reflection.
