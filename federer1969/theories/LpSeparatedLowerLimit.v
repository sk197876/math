(** Federer (1969), 2.5.7, p. 99: the separating function h supplied by
    2.5.5, p. 96, belongs to L+ because it is measurable and satisfies
    0<=h<=g with g in L+. We make the domination argument explicit:
    measurable lower limits alone do not establish Lp membership. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasurableFunctionUP FunctionLatticeUP DaniellIntegralUP DaniellVariationUP
  ExtendedLowerLimitUP ExtendedLowerLimit TotalScalarLpUP TotalScalarLpClosure
  TotalExtendedLowerLimit RealLowerLimitReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_specified_lower_limit_measurable]: measurability of the
    finite separating lower limit in Federer 2.5.7, p. 99, by 2.3.2(5), p.
    74 The abstract lower-limit specification fixes the values; no new
    choice or construction is used. *)
Lemma real_specified_lower_limit_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : nat -> X -> R) (h : X -> R) :
  (forall n, is_measure_measurable_function mu (total_scalar_function (u n))) ->
  (forall x, is_extended_lower_limit (fun n => (u n x)%:E) (h x)%:E) ->
  is_measure_measurable_function mu (total_scalar_function h).
Proof.
move=> hu hl.
have he : h=real_lower_limit_replacement u.
  apply: funext=> x.
  have hh := extended_lower_limit_unique (hl x) (extended_lower_limit_laws (fun n => (u n x)%:E)).
  rewrite /real_lower_limit_replacement /total_extended_lower_limit -hh; by [].
rewrite he; exact (@real_lower_limit_replacement_measurable R X mu hm u hu).
Qed.

(** Source for [lp_separating_lower_limit_member]: the full Lp membership of
    h in Federer 2.5.7, p. 99 The order-interval conditions provided by
    2.5.5, p. 96, suffice for all exponents including infinity; no arbitrary
    lower-limit closure is asserted. *)
Theorem lp_separating_lower_limit_member (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (g h : X -> R) (u : nat -> X -> R) :
  positive_function_lattice (total_scalar_lp mu p) g ->
  (forall n, lattice_positive_order_interval (positive_function_lattice (total_scalar_lp mu p)) g (u n)) ->
  (forall x, (0 <= h x <= g x)%R) ->
  (forall x, is_extended_lower_limit (fun n => (u n x)%:E) (h x)%:E) ->
  positive_function_lattice (total_scalar_lp mu p) h.
Proof.
move=> hg hu hb hl.
have hmemb n : total_scalar_lp mu p (u n) := (hu n).1.1.
have hmeas := @real_specified_lower_limit_measurable R X mu hm u h (fun n => (hmemb n).2.1) hl.
split; last by move=> x; exact: (andP (hb x)).1.
apply: (@total_scalar_lp_domination R X mu hm p g h hg.1 hmeas)=> x.
rewrite (ger0_norm (andP (hb x)).1) (ger0_norm (hg.2 x)); exact: (andP (hb x)).2.
Qed.
