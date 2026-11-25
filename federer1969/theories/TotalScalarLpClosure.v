(** Federer (1969), 2.5.7, p. 98: vector and order-ideal closure of the
    total scalar Lp space. These supporting consequences retain the
    countably measurable nonzero locus at p=infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP MeasurableTotalBasic
  CountablyMeasurableUP CountablyMeasurableFunctions FunctionLatticeUP TotalScalarLpUP
  TotalScalarMeasurability TotalScalarSupport TotalScalarLpNormOrder TotalScalarLpNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_finite_value]: finiteness of the seminorm on
    L in Federer 2.5.7, p. 98, by membership *)
Lemma total_scalar_lp_finite_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp_norm mu p f \is a fin_num.
Proof.
move=> [hp [hf [hn hc]]].
rewrite (ge0_fin_numE (@total_scalar_lp_norm_nonnegative R X mu hm p f hp hf)); exact: hn.
Qed.

(** Source for [total_scalar_lp_zero]: zero member of the corrected unit
    ball in Federer 2.5.7, p. 98 *)
Lemma total_scalar_lp_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p :
  1 <= p -> total_scalar_lp mu p (fun _ : X => 0%R).
Proof.
move=> hp; split=> //; split.
- exact: (@measurable_total_constant R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0%R).
- split; first by rewrite (@total_scalar_lp_norm_zero R X mu hm p hp) ltry.
  exact: (@countably_measurable_zero_function R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0%R).
Qed.

(** Source for [total_scalar_lp_scale]: vector scalar closure underlying
    Federer 2.5.7, p. 98 All real scalars, including zero, are covered. *)
Lemma total_scalar_lp_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (c : R) (f : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p (fun x => (c*f x)%R).
Proof.
move=> hf.
have hs : is_measure_measurable_function mu (total_scalar_function (fun x => (c*f x)%R)).
  apply: (@total_scalar_continuous_operation R X mu hm f (fun y => (c*y)%R) _ hf.2.1).
  change (continuous (fun y : R^o => (c*y)%R)).
  move=> y; apply: cvgM; [exact: cvg_cst|exact: cvg_id].
have hfin := @total_scalar_lp_finite_value R X mu hm p f hf.
split; first exact: hf.1.
split; first exact: hs.
split.
- rewrite (@total_scalar_lp_norm_scale R X mu hm p c f hf.1 hf.2.1) -(fineK hfin) -EFinM.
  exact: ltry.
- apply: (@total_scalar_countable_support_subset R X mu hm f _ hf.2.2.2 hs)=> x he.
  by rewrite he mulr0.
Qed.

(** Source for [total_scalar_lp_add]: vector additive closure underlying
    Federer 2.5.7, p. 98 The nonzero locus is controlled by a union, so no
    sigma-finiteness of the whole space is imposed. *)
Lemma total_scalar_lp_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p g ->
  total_scalar_lp mu p (fun x => (f x+g x)%R).
Proof.
move=> hf hg.
have hs := @function_lattice_add R X _ (@total_scalar_measurable_lattice R X mu hm) f g hf.2.1 hg.2.1.
have hff := @total_scalar_lp_finite_value R X mu hm p f hf.
have hgf := @total_scalar_lp_finite_value R X mu hm p g hg.
split; first exact: hf.1.
split; first exact: hs.
split.
- apply: le_lt_trans (@total_scalar_lp_norm_triangle R X mu hm p f g hf.1 hf.2.1 hg.2.1) _.
  rewrite -(fineK hff) -(fineK hgf) -EFinD; exact: ltry.
- apply: (@total_scalar_countable_support_union R X mu hm f g _ hf.2.2.2 hg.2.2.2 hs)=> x hf0 hg0.
  by rewrite hf0 hg0 add0r.
Qed.

(** Source for [total_scalar_lp_domination]: supporting ideal property used
    in Federer 2.5.7, pp. 98–99 Measurability of the dominated function is
    explicit; support countability follows. *)
Lemma total_scalar_lp_domination (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  total_scalar_lp mu p f -> is_measure_measurable_function mu (total_scalar_function g) ->
  (forall x, (`|g x| <= `|f x|)%R) -> total_scalar_lp mu p g.
Proof.
move=> hf hg hgf; split; first exact: hf.1.
split; first exact: hg.
split.
- exact: le_lt_trans (@total_scalar_lp_norm_order R X mu hm p g f hf.1 hg hf.2.1 hgf) hf.2.2.1.
- apply: (@total_scalar_countable_support_subset R X mu hm f g hf.2.2.2 hg)=> x hf0.
  apply/eqP; rewrite -normr_eq0 eq_le normr_ge0 andbT.
  have hh := hgf x; by rewrite hf0 normr0 in hh.
Qed.
