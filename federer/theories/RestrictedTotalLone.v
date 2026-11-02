(** Federer (1969), 2.5.10, p. 101: the local L1 space is embedded in the
    original L1 space by zero extension. The norm formula is 2.4.12, p. 86. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureRestriction
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP TotalLoneSummability
  TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalScalarPairing
  TotalScalarLpCharacteristic CharacteristicFunctionSealed TotalScalarCutoff RestrictedIntegralIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_real_integral_cutoff_iff]: supporting
    total real integral formula for the local functional in Federer
    2.5.10, p. 101. Both sides assert actual integrals. *)
Lemma restricted_real_integral_cutoff_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (f : X -> R) a :
  measure_measurable mu B ->
  (is_measure_integral (measure_restrict mu B) (real_total_integrand f) a <->
   is_measure_integral mu (real_total_integrand (total_scalar_cutoff B f)) a).
Proof.
move=> hB; rewrite (@restricted_integral_zero_extension_iff R X mu hm B _ a hB).
split=> hi.
- exact: measure_integral_graph_equivalent (total_scalar_cutoff_integrand_graph B f) hi.
- apply: (@measure_integral_graph_equivalent R X mu _ _ a _ hi)=> x z.
  symmetry; exact: total_scalar_cutoff_integrand_graph.
Qed.

(** Source for [restricted_total_lone_cutoff_iff]: supporting
    L1 membership equivalence in Federer 2.5.10, p. 101.
    Summability supplies countable measurability of each support;
    no countability of the ambient decomposition is assumed. *)
Lemma restricted_total_lone_cutoff_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (f : X -> R) :
  measure_measurable mu B ->
  (total_scalar_lp (measure_restrict mu B) 1 f <-> total_scalar_lp mu 1 (total_scalar_cutoff B f)).
Proof.
move=> hB; have hn := measure_restrict_is_measure hm B; split=> hf.
- have [a ha] := @total_lone_summable_real R X (measure_restrict mu B) hn f hf.
  apply: (@summable_real_total_lone R X mu hm); exists a.
  exact: (proj1 (restricted_real_integral_cutoff_iff hm f a%:E hB) ha).
- have [a ha] := @total_lone_summable_real R X mu hm _ hf.
  apply: (@summable_real_total_lone R X (measure_restrict mu B) hn); exists a.
  exact: (proj2 (restricted_real_integral_cutoff_iff hm f a%:E hB) ha).
Qed.

(** Source for [restricted_total_lone_norm_cutoff]: supporting
    isometry for the local L1 functional in Federer 2.5.10,
    p. 101. The actual integral of the absolute value identifies
    the two seminorms without exposing their constructions. *)
Lemma restricted_total_lone_norm_cutoff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (f : X -> R) :
  measure_measurable mu B -> total_scalar_lp (measure_restrict mu B) 1 f ->
  finite_total_scalar_lp_norm mu 1 (total_scalar_cutoff B f)=
    finite_total_scalar_lp_norm (measure_restrict mu B) 1 f.
Proof.
move=> hB hf; have hn := measure_restrict_is_measure hm B.
have hg := (proj1 (restricted_total_lone_cutoff_iff hm f hB)) hf.
have ha := @total_scalar_lone_absolute_integral R X (measure_restrict mu B) hn f hf.
have hb := (proj1 (restricted_real_integral_cutoff_iff hm (fun x => `|f x|%R) _ hB)) ha.
rewrite -total_scalar_cutoff_absolute in hb.
have he := @total_lone_norm_from_absolute_integral R X mu hm _ _ hg.2.1 hb.
rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm 1 _ hg) in he.
by injection he.
Qed.

(** Source for [total_lone_for_restricted_measure]: supporting
    restriction of a global L1 test to each piece in Federer 2.5.10,
    p. 101. The piece may have infinite measure in this lemma. *)
Lemma total_lone_for_restricted_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (f : X -> R) :
  measure_measurable mu B -> total_scalar_lp mu 1 f ->
  total_scalar_lp (measure_restrict mu B) 1 f.
Proof.
move=> hB hf; apply: (proj2 (restricted_total_lone_cutoff_iff hm f hB)).
exact: (@total_scalar_lp_characteristic_piece R X mu hm 1 B _ f
  (@CharacteristicFunction.laws R X B) hB hf).
Qed.
