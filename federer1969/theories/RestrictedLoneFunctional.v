(** Federer (1969), 2.5.10, p. 101, first paragraph: applying 2.5.7(ii) on
    each finite measurable piece. The local functional applies the original
    one to a zero extension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureRestriction MeasureSplit CountablyMeasurableUP CountablyMeasurableBasic
  FunctionLatticeSeminormUP FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpFiniteSeminorm
  LpFunctionalDensityUP LpLinearFunctionalRepresentation TotalScalarCutoff RestrictedTotalLone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_total_lone_functional]: supporting local
    functional in Federer 2.5.10, p. 101 Only its values on local L1 matter. *)
Definition restricted_total_lone_functional (R : realType) (X : Type)
    (B : set X) (A : (X -> R) -> R) := fun f => A (total_scalar_cutoff B f).

(** Source for [restricted_lone_functional_linear]: supporting
    linearity needed for the local application of 2.5.7(ii) in
    Federer 2.5.10, p. 101. *)
Lemma restricted_lone_functional_linear (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (A : (X -> R) -> R) :
  measure_measurable mu B -> is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  is_linear_functional_on_functions (total_scalar_lp (measure_restrict mu B) 1) (restricted_total_lone_functional B A).
Proof.
move=> hB hA; split.
- move=> f g hf hg; rewrite /restricted_total_lone_functional total_scalar_cutoff_add.
  apply: hA.1; [exact: (proj1 (restricted_total_lone_cutoff_iff hm f hB)) hf|
    exact: (proj1 (restricted_total_lone_cutoff_iff hm g hB)) hg].
- move=> c f hf; rewrite /restricted_total_lone_functional total_scalar_cutoff_scale.
  apply: hA.2; exact: (proj1 (restricted_total_lone_cutoff_iff hm f hB)) hf.
Qed.

(** Source for [restricted_lone_functional_bound]: supporting
    preservation of the operator bound on each finite piece in
    Federer 2.5.10, p. 101. The piece need not be finite
    for this estimate itself. *)
Lemma restricted_lone_functional_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (A : (X -> R) -> R) (M : R) :
  measure_measurable mu B ->
  (forall f, total_scalar_lp mu 1 f -> (`|A f| <= M * finite_total_scalar_lp_norm mu 1 f)%R) ->
  forall f, total_scalar_lp (measure_restrict mu B) 1 f ->
    (`|restricted_total_lone_functional B A f| <= M * finite_total_scalar_lp_norm (measure_restrict mu B) 1 f)%R.
Proof.
move=> hB hb f hf.
have hh := hb _ ((proj1 (restricted_total_lone_cutoff_iff hm f hB)) hf).
by rewrite (restricted_total_lone_norm_cutoff hm hB hf) in hh.
Qed.

(** Source for [finite_piece_lone_functional_density]: the actual local
    density supplied by 2.5.7(ii) in Federer 2.5.10, p. 101 *)
Theorem finite_piece_lone_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (A : (X -> R) -> R) (M : R) :
  measure_measurable mu B -> mu B < +oo -> (0 <= M)%R ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  (forall f, total_scalar_lp mu 1 f -> (`|A f| <= M * finite_total_scalar_lp_norm mu 1 f)%R) ->
  exists k : X -> R, is_lp_functional_density (measure_restrict mu B) 1 +oo
    (restricted_total_lone_functional B A) k /\
    total_scalar_lp_norm (measure_restrict mu B) +oo k <= M%:E.
Proof.
move=> hB hfin hM hA hb; have hn := measure_restrict_is_measure hm B.
have hlin := @restricted_lone_functional_linear R X mu hm B A hB hA.
have hbound := @restricted_lone_functional_bound R X mu hm B A M hB hb.
have hop := @function_operator_seminorm_least_bound R X _ _ _ M hM hbound.
have hX : measure_countably_measurable (measure_restrict mu B) setT.
  apply: (@finite_measurable_set_countably_measurable R X _ setT (measure_measurable_whole hn)).
  by rewrite /measure_restrict setIT.
have hc : (1 : \bar R)=+oo -> False by [].
have [_ [k [hk [he hu]]]] := @lp_linear_functional_representation R X (measure_restrict mu B) hn 1 +oo
  (restricted_total_lone_functional B A) (or_intror (or_introl (conj erefl erefl)))
  hlin (le_lt_trans hop (ltry M)) (fun _ => hX) (fun h => False_rect _ (hc h)).
exists k; split=> //; by rewrite he.
Qed.
