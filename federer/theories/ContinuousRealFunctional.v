(** Federer (1969), 2.4.12, pp. 87–88: the continuous dual and the defining
    dual evaluations of the vector-valued integral. The construction and
    existence of the integral are separate from these abstract
    characterisation and uniqueness laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity
  SeminormNormingFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_continuous_real_functional]: membership in
    the continuous real dual Y* in Federer 2.4.12,
    p. 87. Linearity is carried by the map's type;
    continuity uses the specified norm topology. *)
Definition is_continuous_real_functional (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o}) :=
  continuous (fun y : real_norm_metric_space hN => (a y : real_line_metric R)).

(** Source for [bounded_real_functional_continuous]: supporting
    continuity of the Hahn–Banach norming functionals used for
    the dual embedding in Federer 2.4.12, p. 87. *)
Lemma bounded_real_functional_continuous (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o}) (C : R) :
  (0 <= C)%R -> (forall y, (`|a y| <= C*N y)%R) -> is_continuous_real_functional hN a.
Proof.
move=> hC ha; apply: (@metric_fixed_lipschitz_continuous R
  [the metricType R of real_norm_metric_space hN] [the metricType R of real_line_metric R]
  (fun y => a y) C hC).
move=> x y; change (`|a x-a y| <= C*N (x-y))%R.
by rewrite -linearB; exact: ha.
Qed.

(** Source for [continuous_norming_real_functional]: the norming
    dual functional supporting the isometric embedding of Y
    into Y** in Federer 2.4.12, p. 87. The existing
    finite-valued Hahn–Banach corollary suffices here. *)
Lemma continuous_norming_real_functional (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) y :
  exists a : {linear V -> R^o}, is_continuous_real_functional hN a /\
    (forall z, (`|a z| <= N z)%R) /\ a y=N y.
Proof.
have [a [ha hay]] := seminorm_norming_functional hN.1 y.
exists a; split; last by split.
apply: (@bounded_real_functional_continuous R V N hN a 1%R (ler01)).
by move=> z; rewrite mul1r; exact: ha.
Qed.

(** Source for [continuous_real_functionals_separate]: injectivity of the
    canonical map Y to Y** used in Federer 2.4.12, p. 87. *)
Lemma continuous_real_functionals_separate (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (y z : V) :
  (forall a : {linear V -> R^o}, is_continuous_real_functional hN a -> a y=a z) -> y=z.
Proof.
move=> he; have [a [ha [_ hn]]] := continuous_norming_real_functional hN (y-z)%R.
have hzero : N (y-z)%R = 0%R by rewrite -hn linearB (he a ha) subrr.
have hz := hN.2 _ hzero; by move/eqP: hz; rewrite subr_eq0=> /eqP.
Qed.
