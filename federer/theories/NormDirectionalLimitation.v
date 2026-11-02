(** The normed-space example in Federer (1969), 2.8.9, p. 146. Unit
    directions are separated in a compact sphere, giving a bound independent
    of the center and xi=infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealNormUP NormMetric NormMetricContinuity
  LinearBasis FiniteNormMetricCompactness CompactSeparatedCardinality CardinalInjection
  DirectionalLimitationUP NormDirections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

Section NormedDirections.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [separated_norm_direction_injective]: the passage from points
    to directions is one-to-one in Federer 2.8.9, p. 146, because distinct
    members have directions a positive distance apart. Supporting cardinal
    step *)
Lemma separated_norm_direction_injective (a : M) (eta : R) (B : set M) :
  0 < eta -> B `<=` ~` [set a] -> directionally_separated_from a eta B ->
  {in B &, injective (@norm_direction R V N hN a)}.
Proof.
move=> he hB hs b c hb hc hdir.
apply: contrapT=> hbc.
have h := @separated_norm_directions R V N hN a eta B hB hs b c
  (set_mem hb) (set_mem hc) hbc.
by rewrite hdir mdistxx in h; have := lt_le_trans he h; rewrite ltxx.
Qed.

(** Source for [compact_unit_sphere_directional_limitation]:
    the compact-unit-sphere argument in Federer 2.8.9, p. 146,
    with compactness as an explicit intermediate premise. The
    conclusion uses Federer's original definition and xi=infinity.
    Finite dimension is discharged separately below. *)
Theorem compact_unit_sphere_directional_limitation (eta : R) :
  compact [set x : M | N x = 1] -> 0 < eta <= 1/3 ->
  exists zeta : nat, is_directionally_limited_at (@setT M) +oo%E eta zeta.
Proof.
move=> hcompact /andP [he he3].
have [zeta [hz hbound]] := @compact_separated_cardinal_bound R M 0
  [set x : M | N x = 1] eta hcompact he.
exists zeta; constructor=> //.
- exact: lt0y.
- by apply/andP; split.
- move=> a _ B hB hs.
  have hBa : B `<=` ~` [set a] by move=> b hb; exact: (hB b hb).2.
  pose D := (@norm_direction R V N hN a) @` B.
  have hD : D `<=` [set x : M | N x = 1].
    move=> x [b hb <-]; exact: @norm_direction_unit R V N hN a b (hBa b hb).
  have hsep : forall u v, D u -> D v -> u <> v -> eta <= mdist u v.
    move=> u v [b hb <-] [c hc <-] hne.
    apply: (@separated_norm_directions R V N hN a eta B hBa hs b c hb hc).
    by move=> hbc; apply: hne; rewrite hbc.
  have hcard := hbound D hD hsep.
  have heq := inj_card_eq (@separated_norm_direction_injective a eta B he hBa hs).
  by rewrite (card_le_eql heq) in hcard.
Qed.

(** Source for [finite_norm_unit_sphere_compact]: the compact set of unit
    vectors in Federer 2.8.9, p. 146 It is a closed subset of the compact
    unit ball for any norm on a space with a finite basis. The
    zero-dimensional sphere may be empty. *)
Lemma finite_norm_unit_sphere_compact n (e : 'I_n -> V) :
  is_basis e -> compact [set x : M | N x = 1].
Proof.
move=> he.
have hclosed : closed [set x : M | N x = 1].
  apply: (@preimage_closed M (real_line_metric R)
    (fun x => N x) [set 1]).
  - move=> x _; exact: real_norm_metric_norm_continuous.
  - apply: compact_closed; first exact: metric_hausdorff.
    exact: compact_set1.
apply: (subclosed_compact hclosed (@finite_norm_metric_ball_compact R V N hN n e he 1)).
by move=> x hx; rewrite /= hx.
Qed.

(** Source for [finite_norm_directional_limitation]: the full
    finite-dimensional arbitrary-norm example in Federer 2.8.9, p. 146: for
    every 0<eta<=1/3 there is a positive integer zeta for which the whole
    space is infinity,eta,zeta directionally limited. No strict convexity is
    assumed. *)
Theorem finite_norm_directional_limitation n (e : 'I_n -> V) :
  is_basis e -> forall eta : R, 0 < eta <= 1/3 ->
  exists zeta : nat, is_directionally_limited_at (@setT M) +oo%E eta zeta.
Proof.
move=> he eta heta.
exact: compact_unit_sphere_directional_limitation (finite_norm_unit_sphere_compact he) heta.
Qed.
End NormedDirections.
