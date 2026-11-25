(** Federer (1969), 3.2.7, p. 246:
    compare the finite principal sine branch with the
    full periodic fibre, using only the sealed scalar
    trigonometric laws and actual counting measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground RealTrigonometryUP RealTrigonometrySealed RealTrigonometryBasic
  MappingMultiplicity CountingMeasure CountingInjectionBound CharacteristicFunctionUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sine_principal_source_interval]: the
    closed injective sine branch supporting the first
    example of Federer 3.2.7, p. 246.
    It is an auxiliary source restriction, not a
    strengthening of the printed domain A=R. *)
Definition sine_principal_source_interval (R:realType):set (real_line_metric R):=
  `[-((@RealTrigonometry.half_period R)/2),(@RealTrigonometry.half_period R)/2].

(** Source for [real_sine_no_fibre_off_unit_interval]:
    the sine has range in [-1,1], so every
    actual restricted fibre off this range is empty,
    supporting Federer 3.2.7, p. 246. *)
Lemma real_sine_no_fibre_off_unit_interval (R:realType) (T:set (real_line_metric R)) y:
  ~(`[(-1)%R,1%R]:set (real_line_metric R)) y ->
  @mapping_multiplicity R [the choiceType of real_line_metric R] R (@RealTrigonometry.sine R) T y= 0%E.
Proof.
move=>hy.
have he:mapping_fibre (@RealTrigonometry.sine R) T y=set0.
  apply/seteqP; split=>x; last by case.
  move=>[_ hxy]; exfalso; apply:hy.
  have hh:=real_sine_bound (@RealTrigonometry.laws R) x.
  rewrite hxy ler_norml in hh.
  by rewrite /= in_itv /=.
rewrite /mapping_multiplicity he; exact:measure_empty (counting_measure_is_measure R _).
Qed.

(** Source for [real_sine_principal_branch_multiplicity]:
    unit multiplicity on the closed principal branch,
    supporting the first example in Federer 3.2.7,
    p. 246. The characteristic law is abstract
    and includes both extreme target levels. *)
Theorem real_sine_principal_branch_multiplicity (R:realType) (chi:R->R):
  is_characteristic_function (`[(-1)%R,1%R]:set (real_line_metric R)) chi -> forall y,
  @mapping_multiplicity R [the choiceType of real_line_metric R] R (@RealTrigonometry.sine R)
    ((@sine_principal_source_interval R)) y=(chi y)%:E.
Proof.
move=>hChi y; case:(pselect ((`[(-1)%R,1%R]:set (real_line_metric R)) y))=>hy.
- have hy':=hy; move:hy'; rewrite /= in_itv /= =>/andP[hyl hyu].
  rewrite (characteristic_on_set hChi hy) /mapping_multiplicity
    /sine_principal_source_interval (real_sine_principal_branch_fibre hyl hyu).
  exact:counting_measure_singleton_value.
- by rewrite (real_sine_no_fibre_off_unit_interval _ hy) (characteristic_off_set hChi hy).
Qed.
