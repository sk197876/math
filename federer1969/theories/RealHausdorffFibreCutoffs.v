(** Federer (1969), 2.10.25, pp. 188–189: fibre-mass integrand, its
    reciprocal-cutoff approximants, and the printed alternative
    support/properness hypothesis. The value definitions apply the existing
    opaque Hausdorff and covering-infimum interfaces; no concrete measure
    construction is exposed. Monotonicity and the pointwise supremum are
    proved from those interfaces alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation MetricRealPowerCost
  RealPowerCoverVariants HausdorffFibreCutoffs ExtendedRealOrderTopology ExtendedRealBoundsUP MetricScaleEnvelopeUP
  MetricScaleEnvelope MetricScaleEnvelopeLaws HausdorffLengthUP HausdorffDiameterCost
  HausdorffMeasureUP HausdorffMeasure CaratheodoryLimitUP CaratheodoryBorelRegular
  LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_fibre_mass]: direct integrand
    H^k(A intersect f inverse of y) in 2.10.25,
    p. 188. This is an abbreviation using the
    existing abstract Hausdorff measure, not a new
    construction or a measurability assertion. *)
Definition real_hausdorff_fibre_mass (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) (y : Y) : extended_real_line R :=
  @real_hausdorff_measure R X k hk (A `&` f @^-1` [set y]).

(** Source for [real_hausdorff_fibre_cutoff]: direct cutoff integrand
    phi^k_(1/i)(A intersect f inverse of y) in the
    last display of the proof of 2.10.25, p. 189.
    Natural index n represents the positive book index
    n+1. The infimum operator is already sealed. *)
Definition real_hausdorff_fibre_cutoff (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) (n : nat) (y : Y) : extended_real_line R :=
  @metric_scale_envelope R X (@nonempty_metric_sets R X) (fun j=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) ((n.+1%:R : R)^-1)%R%:E
    (A `&` f @^-1` [set y]).

(** Source for [real_hausdorff_fibre_integral_condition]: direct
    alternative hypothesis after the inequality in 2.10.25,
    p. 188. The positive fibre-mass support has a
    countable finite-H^m-mass cover, or the target is
    boundedly compact. Cover members need not be
    assumed measurable. This predicate is not an axiom. *)
Definition real_hausdorff_fibre_integral_condition (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :=
  (exists B : nat -> set Y, (forall n, @real_hausdorff_measure R Y m hm (B n)< +oo) /\
    [set y | 0<real_hausdorff_fibre_mass f A hk y] `<=` \bigcup_n B n) \/ metric_boundedly_compact Y.

(** Source for [real_hausdorff_fibre_cutoff_nonnegative]: supporting
    nonnegative integrands in the proof of 2.10.25,
    p. 189, by the infimum laws of 2.10.1,
    p. 170. No integrand measurability is asserted. *)
Lemma real_hausdorff_fibre_cutoff_nonnegative (R : realType) (X Y : metricType R)
    (f : X -> Y) A (k : R) (hk : (0<=k)%R) n y : 0<=real_hausdorff_fibre_cutoff f A hk n y.
Proof.
rewrite /real_hausdorff_fibre_cutoff.
exact: (metric_scale_envelope_nonnegative (metric_scale_envelope_specification _ _ _)).
Qed.

(** Source for [real_hausdorff_fibre_cutoffs_increasing]: supporting
    increasing cutoff masses in the last step of
    2.10.25, p. 189. Monotonicity follows from the
    abstract covering-infimum laws and reciprocal order. *)
Theorem real_hausdorff_fibre_cutoffs_increasing (R : realType) (X Y : metricType R)
    (f : X -> Y) A (k : R) (hk : (0<=k)%R) n m : (n<=m)%N -> forall y,
  real_hausdorff_fibre_cutoff f A hk n y<=real_hausdorff_fibre_cutoff f A hk m y.
Proof.
move=> hnm y.
exact: (@metric_scale_envelope_antitone_cutoff R X (@nonempty_metric_sets R X)
  (fun j=>val j) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) ((m.+1%:R : R)^-1)%R%:E
  ((n.+1%:R : R)^-1)%R%:E _ _ (metric_scale_envelope_specification _ _ _)
  (metric_scale_envelope_specification _ _ _) (@fibre_reciprocal_cutoff_antitone R n m hnm)
  (A `&` f @^-1` [set y])).
Qed.

(** Source for [real_hausdorff_fibre_cutoffs_supremum]: supporting
    pointwise recovery of H^k fibre mass in the last
    line of the proof of 2.10.25, p. 189.
    The abstract supremum laws include infinite fibre
    mass, and cofinality permits every positive cutoff. *)
Theorem real_hausdorff_fibre_cutoffs_supremum (R : realType) (X Y : metricType R)
    (f : X -> Y) A (k : R) (hk : (0<=k)%R) y :
  is_extended_real_supremum ((fun n=>real_hausdorff_fibre_cutoff f A hk n y) @` setT)
    (real_hausdorff_fibre_mass f A hk y).
Proof.
pose S := fun j : @nonempty_metric_sets R X=>val j.
pose c := fun j : @nonempty_metric_sets R X=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j).
have hpsi := @real_hausdorff_measure_specification R X k hk.
constructor.
- move=> z [n _ <-].
  exact: (@caratheodory_limit_upper R X _ S c (@real_hausdorff_measure R X k hk) hpsi
    (A `&` f @^-1` [set y]) _ _ (@reciprocal_metric_cutoff_positive R n)
    (metric_scale_envelope_specification _ _ _)).
- move=> b hb; apply: (caratheodory_limit_least hpsi)=> delta nu hd hn.
  have [n hcut] := reciprocal_metric_cutoffs_cofinal hd.
  have hh := @metric_scale_envelope_antitone_cutoff R X _ S c
    ((n.+1%:R : R)^-1)%R%:E delta _ nu (metric_scale_envelope_specification _ _ _) hn hcut
    (A `&` f @^-1` [set y]).
  apply: le_trans hh _; apply: hb; by exists n.
Qed.
