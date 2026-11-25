(** Federer (1969), 2.10.24, pp. 186–187: consequences of the weighted
    covering infimum. These proofs use only its order laws and the existing
    almost-everywhere convention; no representation of the infimum or
    integral equality is assumed. Source context:
    WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP NonnegativeSum MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_envelope_nonnegative]: supporting
    nonnegative-infimum observation in 2.10.24,
    p. 186: every weighted covering cost is
    a nonnegative numerical sum. *)
Lemma weighted_metric_envelope_nonnegative (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) :
  is_weighted_metric_envelope S c psi delta lambda -> forall f, 0<=lambda f.
Proof.
move=> hl f; apply: (weighted_metric_envelope_greatest hl)=> G u hG.
exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [weighted_metric_envelope_unique]: supporting
    uniqueness of the abstract infimum specified in
    2.10.24, p. 186. *)
Lemma weighted_metric_envelope_unique (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda xi : (X -> \bar R) -> \bar R) :
  is_weighted_metric_envelope S c psi delta lambda ->
  is_weighted_metric_envelope S c psi delta xi -> lambda=xi.
Proof.
move=> hl hx; apply: funext=> f; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (weighted_metric_envelope_greatest hx)=> G u hG; exact: (weighted_metric_envelope_lower hl hG).
- apply: (weighted_metric_envelope_greatest hl)=> G u hG; exact: (weighted_metric_envelope_lower hx hG).
Qed.

(** Source for [weighted_metric_envelope_antitone_cutoff]: direct
    monotonicity display in 2.10.24, p. 187:
    a smaller diameter cutoff gives a larger
    weighted infimum. The order proof itself also
    permits other extended cutoffs. *)
Theorem weighted_metric_envelope_antitone_cutoff (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (delta eta : \bar R) (lambda xi : (X -> \bar R) -> \bar R) :
  is_weighted_metric_envelope S c psi delta lambda ->
  is_weighted_metric_envelope S c psi eta xi -> delta<=eta -> forall f, xi f<=lambda f.
Proof.
move=> hl hx hde f; apply: (weighted_metric_envelope_greatest hl)=> G u hG.
apply: (weighted_metric_envelope_lower hx); constructor.
- exact: weighted_metric_cover_countable hG.
- exact: weighted_metric_cover_nonnegative hG.
- move=> j hj; exact: le_trans (weighted_metric_cover_diameter hG hj) hde.
- exact: weighted_metric_cover_dominates hG.
Qed.

(** Source for [weighted_metric_envelope_mono]: supporting
    domination comparison for the weighted infimum
    of 2.10.24, p. 186. Only almost
    assertions require the measure laws of psi;
    no measurability of f or g is assumed. *)
Theorem weighted_metric_envelope_mono (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) (f g : X -> \bar R) :
  is_measure psi -> is_weighted_metric_envelope S c psi delta lambda ->
  (forall x, f x<=g x) -> lambda f<=lambda g.
Proof.
move=> hm hl hfg; apply: (weighted_metric_envelope_greatest hl)=> G u hG.
apply: (weighted_metric_envelope_lower hl); constructor.
- exact: weighted_metric_cover_countable hG.
- exact: weighted_metric_cover_nonnegative hG.
- exact: weighted_metric_cover_diameter hG.
- apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ (weighted_metric_cover_dominates hG)).
  move=> x hx; exact: le_trans (hfg x) hx.
Qed.

(** Source for [weighted_metric_envelope_approximation]: supporting
    near-optimal G_j,u_j choices in 2.10.24,
    p. 187. A strict upper bound on
    the infimum suffices; an attained minimum is
    not claimed, and nonexistent covers retain value infinity. *)
Theorem weighted_metric_envelope_approximation (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) (f : X -> \bar R) (b : \bar R) :
  is_weighted_metric_envelope S c psi delta lambda -> lambda f<b ->
  exists G u, is_weighted_metric_cover S psi delta f G u /\ weighted_generator_cost c G u<b.
Proof.
move=> hl hb; apply: contrapT=> hnone.
have hle : b<=lambda f.
  apply: (weighted_metric_envelope_greatest hl)=> G u hG.
  rewrite leNgt; apply/negP=> hlt; apply: hnone; exists G,u; by split.
by have hh := lt_le_trans hb hle; rewrite ltxx in hh.
Qed.

(** Source for [weighted_metric_envelope_zero]: supporting
    zero-function boundary of 2.10.24, p. 186.
    The empty weighted cover has cost zero and
    dominates zero everywhere, without a generator chosen
    as padding or any finite-total-mass assumption. *)
Lemma weighted_metric_envelope_zero (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) :
  is_measure psi -> is_weighted_metric_envelope S c psi delta lambda -> lambda (fun _=>0)=0.
Proof.
move=> hm hl.
pose u := fun _ : J=>(0%R : R).
have hpoint x : weighted_generator_sum S set0 u x=0.
  have he : [set j | set0 j /\ S j x]=(@set0 J) by apply/seteqP; split=> [j [[] _]|j []].
  by rewrite /weighted_generator_sum he nonnegative_sum_empty.
have hcover : is_weighted_metric_cover S psi delta (fun _=>0) set0 u.
  constructor.
  - exact: countable0.
  - by move=> j [].
  - by move=> j [].
  - apply: (@measure_almost_everywhere_mono R X psi hm setT _ _ (measure_almost_everywhere_true hm)).
    move=> x _; change (is_true (0<=weighted_generator_sum S set0 u x)); by rewrite hpoint.
have hh := weighted_metric_envelope_lower hl hcover.
rewrite /weighted_generator_cost nonnegative_sum_empty in hh.
apply/eqP; by rewrite eq_le hh (weighted_metric_envelope_nonnegative hl).
Qed.
