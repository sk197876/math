(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureDerivationContext MetricClosedBalls CenteredRatioInfinity
  NullBallLocus CenteredRatioBorel ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [has_arbitrarily_small_lower_ball_ratio]: supporting
    operational form of the lower-ratio cutoff in Federer
    2.9.15, p. 160, last proof paragraph. Every positive
    radius cap admits a smaller positive centered ball whose
    numerator mass is less than c times the reference mass. *)
Definition has_arbitrarily_small_lower_ball_ratio (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (c : R) :=
  forall e : R, (0<e)%R -> exists r : R, (0<r)%R /\ (r<e)%R /\
    psi (metric_closed_ball x r)<c%:E*phi (metric_closed_ball x r).

(** Source for [small_lower_ball_ratio_reciprocal]: supporting
    reciprocal-radius encoding of the countable cutoff step
    in Federer 2.9.15, p. 160. Cofinality of positive
    reciprocal natural radii is independent of measurability. *)
Lemma small_lower_ball_ratio_reciprocal (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (c : R) :
  has_arbitrarily_small_lower_ball_ratio psi phi x c <->
    forall k, centered_ratio_below_points psi phi c ((k.+1%:R : R)^-1)%R x.
Proof.
split.
- move=> h k; have [r [hr [hrk hb]]] := h ((k.+1%:R : R)^-1)%R
    (ltac:(by rewrite invr_gt0 ltr0n)).
  exists r; by split; first split.
- move=> h e he; have [k hk] := @positive_reciprocal_nat_small R e he.
  have [r [[hr hrk] hb]] := h k.
  exists r; split=> //; split=> //; exact: lt_trans hrk hk.
Qed.

(** Source for [outside_infinite_density_small_comparison]: direct
    countable lower-ratio reduction in Federer 2.9.15,
    p. 160, last proof paragraph. Outside W and P there
    is a positive natural coefficient admitting arbitrarily
    small strict lower-comparison balls. The proof uses the
    exact countable formula for W, retaining partial division. *)
Lemma outside_infinite_density_small_comparison (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  ~ measure_infinite_centered_density_points psi phi x ->
  exists n, has_arbitrarily_small_lower_ball_ratio psi phi x (n.+1%:R : R).
Proof.
move=> hphi hnP hnW; apply: contrapT=> hn.
apply: hnW; rewrite (@infinite_centered_density_countable_formula R X psi phi hphi).
split=> // n _; apply: contrapT=> hnone.
apply: hn; exists n; apply: (small_lower_ball_ratio_reciprocal psi phi x _).2=> k.
apply: contrapT=> hnot; apply: hnone; by exists k.
Qed.
