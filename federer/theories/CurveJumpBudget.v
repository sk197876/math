(** Federer (1969), 2.10.14, p. 177: the two jump sums are nonnegative
    numerical sums over [a,b) and (a,b]. Access them through the sealed
    weighted counting-measure interface. Retraction to [a,b] converts these
    exact ranges into the global jump sums of the representative. The upper
    integral is corrected in erratum p. 3, book p. 177 line 23; the jump
    ranges are unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground CurveOneSidedJumpUP CurveOneSidedJumpContinuity
  CurveJumpLocalization StieltjesSubstitution WeightedCountingMeasure MeasureUP MeasureBasic
  NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd NonnegativeSumRestriction NonnegativeSumCountable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_jump_measure]: supporting atomic measure
    with singleton weights alpha_+ or alpha_- for the sums
    in 2.10.14, p. 177. It is the public sealed weighted
    counting measure, used through its defining finite-sum laws. *)
Definition curve_jump_measure (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) :=
  @weighted_counting_measure R [the choiceType of real_line_metric R]
    (curve_one_sided_jump g right).

(** Source for [curve_jump_measure_sum]: direct numerical-sum
    interpretation of the atomic budgets in 2.10.14, p. 177. *)
Lemma curve_jump_measure_sum (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (A : set (real_line_metric R)) :
  curve_jump_measure g right A=nonnegative_sum A (curve_one_sided_jump g right).
Proof. exact: weighted_counting_measure_sum. Qed.

(** Source for [curve_jump_measure_is_measure]: supporting measure
    law for the nonnegative jump budgets in 2.10.14, p. 177. *)
Lemma curve_jump_measure_is_measure (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) : is_measure (curve_jump_measure g right).
Proof. apply: weighted_counting_measure_is_measure=> x; exact: curve_one_sided_jump_nonnegative. Qed.

(** Source for [curve_jump_measure_all_sets_measurable]: supporting
    additivity of the jump budgets in 2.10.14, p. 177.
    Every source set is measurable for this atomic measure. *)
Lemma curve_jump_measure_all_sets_measurable (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (A : set (real_line_metric R)) :
  measure_measurable (curve_jump_measure g right) A.
Proof. apply: weighted_counting_measure_measurable=> x; exact: curve_one_sided_jump_nonnegative. Qed.

(** Source for [curve_interval_jump_budget]: direct sum of the two
    numerical sums in 2.10.14, p. 177. The right jump at
    a and the left jump at b are included; the opposite
    exterior-facing endpoint jumps are omitted. *)
Definition curve_interval_jump_budget (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) :=
  curve_jump_measure g true `[a,b[+curve_jump_measure g false `]a,b].

(** Source for [curve_interval_jump_budget_nonnegative]: supporting
    nonnegativity of the jump contribution in 2.10.14, p. 177,
    including divergent sums. *)
Lemma curve_interval_jump_budget_nonnegative (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : 0<=curve_interval_jump_budget g a b.
Proof.
apply: adde_ge0.
- exact: (@measure_nonnegative R [the choiceType of real_line_metric R] _
    (curve_jump_measure_is_measure g true) `[a,b[).
- exact: (@measure_nonnegative R [the choiceType of real_line_metric R] _
    (curve_jump_measure_is_measure g false) `]a,b]).
Qed.

(** Source for [curve_right_jump_global_retraction]: supporting
    exact interval locality of the right sum in 2.10.14,
    p. 177: the retracted curve's global right budget equals
    the original right budget over [a,b), including infinite values. *)
Theorem curve_right_jump_global_retraction (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<=b)%R ->
  curve_jump_measure (g \o @segment_retraction R a b) true setT=
    curve_jump_measure g true `[a,b[.
Proof.
move=> hab; rewrite !curve_jump_measure_sum.
have he : nonnegative_sum setT (curve_one_sided_jump (g \o @segment_retraction R a b) true)=
    nonnegative_sum setT (fun x => if x \in (`[a,b[ : set (real_line_metric R))
      then curve_one_sided_jump g true x else 0).
  apply: nonnegative_sum_ext=> x hx.
  rewrite -/(curve_right_jump_size _ x) (@curve_right_jump_retracted R Y g a b x hab).
  have hi : (x \in (`[a,b[ : set (real_line_metric R)))=(a<=x<b)%R.
    apply/idP/idP; [by move=> /set_mem hxI|move=> hxI; exact: mem_set hxI].
  by rewrite hi.
by rewrite he nonnegative_sum_restrict setTI.
Qed.

(** Source for [curve_left_jump_global_retraction]: supporting
    exact interval locality of the left sum in 2.10.14,
    p. 177, with the required (a,b] endpoint convention. *)
Theorem curve_left_jump_global_retraction (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<=b)%R ->
  curve_jump_measure (g \o @segment_retraction R a b) false setT=
    curve_jump_measure g false `]a,b].
Proof.
move=> hab; rewrite !curve_jump_measure_sum.
have he : nonnegative_sum setT (curve_one_sided_jump (g \o @segment_retraction R a b) false)=
    nonnegative_sum setT (fun x => if x \in (`]a,b] : set (real_line_metric R))
      then curve_one_sided_jump g false x else 0).
  apply: nonnegative_sum_ext=> x hx.
  rewrite -/(curve_left_jump_size _ x) (@curve_left_jump_retracted R Y g a b x hab).
  have hi : (x \in (`]a,b] : set (real_line_metric R)))=(a<x<=b)%R.
    apply/idP/idP; [by move=> /set_mem hxI|move=> hxI; exact: mem_set hxI].
  by rewrite hi.
by rewrite he nonnegative_sum_restrict setTI.
Qed.

(** Source for [curve_jump_exception_set]: supporting locus of
    nonzero combined one-sided jump in 2.10.14, p. 177.
    Nonnegativity makes its complement exactly the continuity locus. *)
Definition curve_jump_exception_set (R : realType) (Y : metricType R)
    (g : R -> Y) : set (real_line_metric R) :=
  [set x | curve_one_sided_jump g true x+curve_one_sided_jump g false x!=0].

(** Source for [finite_global_jump_budget_countable]: supporting
    countability of possible discontinuities for 2.10.14, p. 177,
    when the two global jump sums are finite. Apply 2.1.1(12),
    p. 53, to their nonnegative combined summand. *)
Theorem finite_global_jump_budget_countable (R : realType) (Y : metricType R)
    (g : R -> Y) : curve_jump_measure g true setT+curve_jump_measure g false setT< +oo ->
  countable (curve_jump_exception_set g).
Proof.
rewrite !curve_jump_measure_sum -nonnegative_sum_add; last first.
- move=> x hx; exact: curve_one_sided_jump_nonnegative.
- move=> x hx; exact: curve_one_sided_jump_nonnegative.
move=> hs.
have hnon x : setT x -> 0<=curve_one_sided_jump g true x+curve_one_sided_jump g false x.
  move=> hx; apply: adde_ge0; exact: curve_one_sided_jump_nonnegative.
have hc := @nonnegative_sum_countable_support R [the choiceType of real_line_metric R]
  setT (fun x => curve_one_sided_jump g true x+curve_one_sided_jump g false x) hnon hs.
by rewrite setTI in hc.
Qed.

(** Source for [curve_continuous_off_jump_exception_set]: supporting
    continuity off the jump locus in 2.10.14, p. 177.
    If the sum of two nonnegative jumps is zero, each vanishes;
    the proved one-sided epsilon criteria then give continuity. *)
Theorem curve_continuous_off_jump_exception_set (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : ~ curve_jump_exception_set g x -> g @ x --> g x.
Proof.
move=> hx.
have he : curve_one_sided_jump g true x+curve_one_sided_jump g false x=0.
  case: (eqVneq (curve_one_sided_jump g true x+curve_one_sided_jump g false x) 0)=> he; first exact he.
  exfalso; exact: hx he.
have hr := @curve_one_sided_jump_nonnegative R Y g true x.
have hl := @curve_one_sided_jump_nonnegative R Y g false x.
have hrb : curve_one_sided_jump g true x<=0.
  rewrite -he; exact: lee_paddr hl (lexx _).
have hlb : curve_one_sided_jump g false x<=0.
  rewrite -he; exact: lee_paddl hr (lexx _).
apply/(curve_jump_zero_continuous_iff g x); split; apply/eqP; by rewrite eq_le ?hrb ?hlb ?hr ?hl.
Qed.
