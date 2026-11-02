(** Federer (1969), 2.4.3(3), p. 82: nonnegative functions have nonnegative
    upper integral. Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds PartialExtendedOrderLoci MeasureStepNonnegative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_integral_nonnegative]: direct
    Federer 2.4.3(3), p. 82; f need not be measurable. *)
Theorem measure_upper_integral_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> 0 <= measure_upper_integral mu f.
Proof.
move=> hf; apply: (measure_upper_integral_specification mu f).2=> a [u [[hu huf] ha]].
apply: (@measure_step_integral_nonnegative R X mu hm u a _ ha).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hf huf)).
move=> x [[z [hz hpos]] [y [w [hy [hw hwy]]]]].
have ezw : z=w := partial_function_single_valued hz hw.
exists y; split=> //.
have h : (0 : \bar R) <= y%:E by apply: le_trans _ hwy; by rewrite -ezw.
by rewrite lee_fin in h.
Qed.
