(** Public integral interface and defining equivalences for Federer (1969),
    2.4.2, p. 81. The integral's value is obtained only from the sealed
    specification; its two order bounds and proof independence follow from
    uniqueness. Source context: MeasureIntegralUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralBounds MeasureIntegralSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral]: the assigned integral of
    an integrable function in Federer 2.4.2, p. 81. *)
Definition measure_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) :=
  @MeasureIntegral.value R X mu f hf.

(** Source for [measure_integral_specification]: the public
    integral obeys the defining laws of Federer 2.4.2, p. 81. *)
Lemma measure_integral_specification (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) :
  is_measure_integral mu f (measure_integral hf).
Proof. exact: MeasureIntegral.laws. Qed.

(** Source for [measure_integrable_iff_bounds_equal]: direct
    integrability criterion in Federer 2.4.2, p. 81:
    measurability and equality of upper and lower integrals. *)
Theorem measure_integrable_iff_bounds_equal (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) :
  is_measure_integrable mu f <-> is_measure_measurable_function mu f /\
    measure_upper_integral mu f = measure_lower_integral mu f.
Proof.
split.
- move=> [a [hm [hu hl]]]; split=> //.
  have eu := @measure_upper_integral_unique R X mu f _ a (measure_upper_integral_specification mu f) hu.
  have el := @measure_lower_integral_unique R X mu f _ a (measure_lower_integral_specification mu f) hl.
  by rewrite eu el.
- move=> [hm he]; exists (measure_upper_integral mu f); split=> //; split.
  + exact: measure_upper_integral_specification.
  + rewrite he; exact: measure_lower_integral_specification.
Qed.

(** Source for [measure_integral_upper]: the integral equals
    the upper integral in Federer 2.4.2, p. 81, defining display. *)
Lemma measure_integral_upper (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) :
  measure_integral hf = measure_upper_integral mu f.
Proof.
exact: measure_upper_integral_unique (measure_integral_specification hf).2.1
  (measure_upper_integral_specification mu f).
Qed.

(** Source for [measure_integral_lower]: the integral equals
    the lower integral in Federer 2.4.2, p. 81, defining display. *)
Lemma measure_integral_lower (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) :
  measure_integral hf = measure_lower_integral mu f.
Proof.
exact: measure_lower_integral_unique (measure_integral_specification hf).2.2
  (measure_lower_integral_specification mu f).
Qed.

(** Source for [measure_integral_proof_independent]: supporting
    well-definedness of the assignment in Federer 2.4.2, p. 81. *)
Lemma measure_integral_proof_independent (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (hf hg : is_measure_integrable mu f) :
  measure_integral hf = measure_integral hg.
Proof. by rewrite !measure_integral_upper. Qed.

(** Source for [measure_summable_iff_finite_integral]: direct
    summability condition in Federer 2.4.2, p. 81, final sentence. *)
Theorem measure_summable_iff_finite_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) :
  is_measure_summable mu f <-> measure_integral hf \is a fin_num.
Proof.
split.
- move=> [a ha].
  have he := @measure_integral_unique R X mu f _ a%:E (measure_integral_specification hf) ha.
  by rewrite he.
- move=> hfin; exists (fine (measure_integral hf)).
  rewrite fineK //; exact: measure_integral_specification.
Qed.
