(** Federer (1969), 2.1.5(5), p. 57: classification of measurable sets for
    restriction to a set of finite measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureHull MeasureRestriction
  MeasureRestrictionSupport MeasureFiniteClosure RegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_measure_restricted_subset_representative]:
    Federer 2.1.5(5), proof p. 57: a restricted measurable subset
    A of S is B intersection S for some originally measurable B.
    The proof chooses hulls, proves the excess intersection null,
    and removes that excess from a measurable superset. *)
Lemma regular_measure_restricted_subset_representative (R : realType)
    (I : choiceType) (mu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_regular_measure mu) (S A : set I) :
  mu S < +oo -> A `<=` S -> measure_measurable (measure_restrict mu S) A ->
  exists B, measure_measurable mu B /\ B `&` S = A.
Proof.
move=> hf hAS hA.
have [S' hS] := @regular_measure_finite_hull R I mu hm hr S hf.
have [D [hAD [hD hDA]]] := hr A.
pose A' := D `&` S'.
have hAp : measure_measurable mu A' := @measure_measurable_intersection R I mu hm _ _ hD (measure_hull_measurable hS).
have hAA : A `<=` A'.
  move=> x hx; split; first exact: hAD.
  exact: (@measure_hull_subset R I mu S S' hS x (hAS x hx)).
have hAS' : A' `<=` S' by move=> x [_ hx].
have hval : mu A' = mu A.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite hDA; apply: (@measure_mono R I mu hm _ _)=> x [hx _]; exact hx.
  - exact: (@measure_mono R I mu hm _ _ hAA).
pose nu := measure_restrict mu S.
have hn : is_measure nu := measure_restrict_is_measure hm S.
have hnuA : nu A = mu A := @measure_restrict_subset_value R I mu S A hAS.
have hnuAp : nu A' = mu A.
  rewrite /nu /measure_restrict (setIC S A') (measure_hull_test hS hAp) (setIC A' S').
  have he : S' `&` A' = A'.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hAS'.
  by rewrite he hval.
have hfin : nu A \is a fin_num.
  rewrite hnuA ge0_fin_numE; last exact: (@measure_nonnegative R I mu hm).
  exact: le_lt_trans (@measure_mono R I mu hm A S hAS) hf.
have hzero : nu (A' `\` A) = 0.
  have hi : A' `&` A = A.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hAA.
  have h := hA A'; change (nu A' = nu (A' `&` A) + nu (A' `\` A)) in h.
  rewrite hi hnuAp -hnuA in h.
  have he := congr1 (fun t => t - nu A) h.
  by rewrite subee // (addeC (nu A) (nu (A' `\` A))) addeK // in he.
pose N := (A' `&` S) `\` A.
have hN : mu N = 0.
  have he : N = S `&` (A' `\` A) by rewrite /N setIDA (setIC S A').
  by rewrite he; exact hzero.
have hNm := @measure_null_measurable R I mu hm N hN.
exists (A' `\` N); split.
- exact: (@measure_measurable_difference R I mu hm A' N hAp hNm).
- apply/seteqP; split.
  + move=> x [[ha hn0] hs]; case: (pselect (A x))=> hx //.
    exfalso; apply: hn0; split=> //; by split.
  + move=> x hx; split; last exact: hAS.
    split; first exact: hAA.
    by move=> [_ hn0]; exact: hn0.
Qed.

(** Source for [regular_measure_restriction_measurable_iff]:
    Federer 2.1.5(5), p. 57: the restricted measurable sets are
    exactly (B intersection S) union C, with B originally measurable
    and C contained in the complement of S. No original measurability
    condition on S or C is imposed. *)
Theorem regular_measure_restriction_measurable_iff (R : realType)
    (I : choiceType) (mu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_regular_measure mu) (S A : set I) : mu S < +oo ->
  (measure_measurable (measure_restrict mu S) A <->
    exists B C, measure_measurable mu B /\ C `<=` ~` S /\ A = (B `&` S) `|` C).
Proof.
move=> hf; pose nu := measure_restrict mu S.
have hn : is_measure nu := measure_restrict_is_measure hm S.
have hS : measure_measurable nu S := measure_restrict_support_measurable hm S.
split.
- move=> hA.
  have hY : measure_measurable nu (A `&` S) := @measure_measurable_intersection R I nu hn A S hA hS.
  have hYS : A `&` S `<=` S by move=> x [_ hx].
  have [B [hB he]] := @regular_measure_restricted_subset_representative R I mu hm hr S (A `&` S) hf hYS hY.
  exists B, (A `\` S); split=> //; split; first by move=> x [_ hx].
  rewrite he; apply/seteqP; split.
  + move=> x hx; case: (pselect (S x))=> hs; [left | right]; by split.
  + by move=> x [[hx _]|[hx _]].
- move=> [B [C [hB [hC ->]]]].
  have hBn : measure_measurable nu B := @measure_restrict_measurable R I mu S B hB.
  have hBS := @measure_measurable_intersection R I nu hn B S hBn hS.
  have hCn : measure_measurable nu C.
    apply: (@measure_null_measurable R I nu hn C).
    exact: (@measure_restrict_outside_null R I mu hm S C hC).
  exact: (@measure_measurable_union R I nu hn _ _ hBS hCn).
Qed.
