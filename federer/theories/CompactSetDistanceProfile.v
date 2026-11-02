(** Federer (1969), 2.10.21, p. 183: the map Omega sends a nonempty compact
    set to its distance function. Use the already sealed infimum of 2.2.10;
    only its defining laws are visible. They do not state this hyperspace
    result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import MetricSetDistanceUP MetricSetDistanceSealed MetricSetDistanceBasic
  MetricSetDistanceClosure MetricSetDistanceContinuity LipschitzUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_set]: direct family F
    of all nonempty compact subsets in 2.10.21,
    p. 183. Compactness is relative to the given
    metric topology, with no bounded compactness assumed yet. *)
Definition compact_metric_set (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type [set A : set X | compact A /\ A !=set0]].

(** Source for [compact_set_distance_profile]: direct
    Omega_C of 2.10.21, p. 183, accessed
    through the existing sealed distance infimum. *)
Definition compact_set_distance_profile (R : realType) (X : metricType R)
    (C : compact_metric_set X) : X -> R :=
  @MetricSetDistance.value R X (val C) (set_valP C).2.

(** Source for [compact_set_distance_profile_specification]: supporting
    infimum laws for Omega_C in 2.10.21, p. 183. *)
Lemma compact_set_distance_profile_specification (R : realType) (X : metricType R)
    (C : compact_metric_set X) :
  is_metric_set_distance (val C) (compact_set_distance_profile C).
Proof. exact: MetricSetDistance.laws. Qed.

(** Source for [compact_set_distance_profile_lipschitz]: direct membership
    Omega_C in E_1 in 2.10.21, p. 183. The bound follows from the infimum
    laws. *)
Lemma compact_set_distance_profile_lipschitz (R : realType) (X : metricType R)
    (C : compact_metric_set X) :
  is_metric_lipschitz_bound setT (compact_set_distance_profile C : X -> real_line_metric R) 1.
Proof.
split; first exact: ler01.
move=> x y _ _; rewrite real_line_metric_distanceE mul1r.
exact: metric_set_distance_lipschitz_one (compact_set_distance_profile_specification C) x y.
Qed.

(** Source for [compact_set_distance_profile_zero]: direct
    zero-set identity C={x:Omega_C(x)=0} in
    2.10.21, p. 183. Compact subsets of a
    metric space are closed. *)
Lemma compact_set_distance_profile_zero (R : realType) (X : metricType R)
    (C : compact_metric_set X) x : compact_set_distance_profile C x=0 <-> val C x.
Proof.
have hc := compact_closed (@metric_hausdorff R X) (set_valP C).1.
split.
- move=> hz; apply: hc; exact: (proj1 (metric_set_distance_zero_closure
    (compact_set_distance_profile_specification C) x) hz).
- exact: metric_set_distance_member (compact_set_distance_profile_specification C) x.
Qed.

(** Source for [compact_set_distance_profile_injective]: direct
    univalence of Omega in 2.10.21, p. 183.
    This holds for every metric space, before the
    bounded compactness hypothesis is needed. *)
Theorem compact_set_distance_profile_injective (R : realType) (X : metricType R) :
  injective (@compact_set_distance_profile R X).
Proof.
move=> C D he; apply: val_inj; apply/seteqP; split=> x hx.
- apply: (proj1 (compact_set_distance_profile_zero D x)); rewrite -he.
  exact: (proj2 (compact_set_distance_profile_zero C x) hx).
- apply: (proj1 (compact_set_distance_profile_zero C x)); rewrite he.
  exact: (proj2 (compact_set_distance_profile_zero D x) hx).
Qed.

(** Source for [compact_distance_profile_signed_bound]: direct
    first displayed supremum identity of 2.10.21,
    p. 183, in equivalent upper-bound form. A
    real bound on Omega_D restricted to C is
    equivalent to a bound on Omega_D minus Omega_C
    on all X. Suprema need not be separately chosen. *)
Theorem compact_distance_profile_signed_bound (R : realType) (X : metricType R)
    (C D : compact_metric_set X) (b : R) :
  (forall x, compact_set_distance_profile D x-compact_set_distance_profile C x<=b) <->
  (forall x, val C x -> compact_set_distance_profile D x<=b).
Proof.
pose c := compact_set_distance_profile C; pose d := compact_set_distance_profile D.
have hc := compact_set_distance_profile_specification C.
have hd := compact_set_distance_profile_specification D.
split.
- move=> h x hx; have hh := h x.
  have hz : c x=0 := metric_set_distance_member hc hx.
  by rewrite /c in hz; rewrite hz subr0 in hh.
- move=> h x.
  have hl : d x-b<=c x.
    apply: (@metric_set_distance_greatest R X (val C) c hc x (d x-b))=> y hy.
    have hdiff : d x-d y<=mdist x y := metric_set_distance_subtract_bound hd x y.
    have hbound := h y hy; change (is_true (d y<=b)) in hbound; lra.
  change (is_true (d x-c x<=b)); lra.
Qed.
