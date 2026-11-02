(** Federer (1969), 2.9.20, p. 166: the first consequent implication of (3)
    bounds the sum of variations by the same epsilon whenever the total
    interval length is at most delta. Source context and conventions:
    RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveArcLength OrderedIntervalFamilyUP
  IntervalFamilyNearVariation RealAbsoluteContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_increment_family_bound_variations]: direct finite
    refinement argument in Federer 2.9.20, p. 166, first consequent
    implication Approximate all cell variations with one eligible refinement
    preserving the total length, then close an arbitrary positive error. The
    original locally finite variation hypothesis is retained. *)
Lemma real_increment_family_bound_variations (R : realType) (g : R -> R)
    (a b d e : R) (s : seq (R * R)) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  (forall t : seq (R * R), is_ordered_real_interval_family a b t ->
    real_interval_family_length t<=d -> real_interval_family_increment_sum g t<=e) ->
  is_ordered_real_interval_family a b s -> real_interval_family_length s<=d ->
  real_interval_family_variation_sum g s<=e.
Proof.
move=> hg hfamily hs hlen; apply/ler_addgt0Pr=> eta heta.
have [t [ht [htLen hgap]]] := ordered_interval_family_near_variation hg hs heta.
have htSmall : real_interval_family_length t<=d by rewrite htLen.
have hb := hfamily t ht htSmall.
lra.
Qed.

(** Source for [real_absolute_continuity_family_variation]: direct first
    consequent implication of condition (3) in Federer 2.9.20, p. 166 The
    same delta furnished by absolute continuity works for sums of the full
    variations, with the printed non-strict inequalities. *)
Theorem real_absolute_continuity_family_variation (R : realType) (g : R -> R)
    (a b : R) : curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_absolutely_continuous_real_curve g a b -> forall e : R, 0<e ->
  exists d : R, 0<d /\ forall s : seq (R * R),
    is_ordered_real_interval_family a b s -> real_interval_family_length s<=d ->
    real_interval_family_variation_sum g s<=e.
Proof.
move=> hg hAC e he; have [d [hd hbound]] := hAC e he.
exists d; split=> // s hs hlen.
exact: real_increment_family_bound_variations hg hbound hs hlen.
Qed.
