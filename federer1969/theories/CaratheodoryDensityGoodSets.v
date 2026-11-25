(** Federer (1969), 2.10.17, p. 179, proof: B(nu,t,delta) consists of points
    of A where the generator bound holds at that cutoff. Restrict to this
    set, then apply part (1). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MeasureUP MeasureBasic CaratheodoryDensityScaleBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_density_good_set]: direct B(nu,t,delta) in the
    proof of 2.10.17, p. 179 The indexed generator family records the same
    pointwise bounds, also with repetitions. *)
Definition caratheodory_density_good_set (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (t : R) (delta : \bar R) :=
  [set x | A x /\ forall j, S j x -> extended_metric_diameter (S j)<=delta -> mu (A `&` S j)<=t%:E*c j].

(** Source for [caratheodory_density_good_set_subset]: supporting
    inclusion B(nu,t,delta) contained in A, implicit in
    the definition in 2.10.17, p. 179. *)
Lemma caratheodory_density_good_set_subset (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (t : R) delta :
  caratheodory_density_good_set S c mu A t delta `<=` A.
Proof. by move=> x [hx _]. Qed.

(** Source for [caratheodory_density_good_set_cutoff]: supporting
    monotonicity of B(nu,t,delta) as delta decreases in 2.10.17, p. 179 *)
Lemma caratheodory_density_good_set_cutoff (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (t : R) delta eta :
  delta<=eta -> caratheodory_density_good_set S c mu A t eta `<=`
    caratheodory_density_good_set S c mu A t delta.
Proof.
move=> hd x [hx hb]; split=> // j hj hdiam; exact: hb j hj (le_trans hdiam hd).
Qed.

(** Source for [caratheodory_density_good_set_bound]: supporting estimate
    nu(B(nu,t,delta))<=t phi_delta(B(nu,t,delta)) in 2.10.17, p. 179. no
    measurability of B is assumed. *)
Theorem caratheodory_density_good_set_bound (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (mu nu : set X -> \bar R) (A : set X) (t : R) delta :
  is_measure mu -> (forall j, 0<=c j) -> (0<t)%R ->
  is_metric_scale_envelope S c delta nu ->
  mu (caratheodory_density_good_set S c mu A t delta)<=
    t%:E*nu (caratheodory_density_good_set S c mu A t delta).
Proof.
move=> hm hc ht hn.
pose B := caratheodory_density_good_set S c mu A t delta.
apply: (@caratheodory_density_scale_bound R X J S c delta nu mu B t hn hm ht)=> j hd.
case: (pselect (exists x, B x /\ S j x))=> [[x [hx hS]]|hno].
- apply: le_trans (@measure_mono R X mu hm _ _ _) (hx.2 j hS hd).
  by move=> y [hy hSy]; split=> //; exact hy.1.
- have he : B `&` S j=set0.
    apply/seteqP; split=> // x [hx hS]; exfalso; apply: hno; by exists x.
  rewrite he (measure_empty hm); apply: mule_ge0; last exact: hc.
  by rewrite lee_fin; exact: ltW ht.
Qed.
