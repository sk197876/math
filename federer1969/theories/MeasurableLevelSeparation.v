(** Federer (1969), 2.3.2(7), p. 74: necessity of the separated-level
    inequality. Split a test set by a measurable closed lower level; the
    upper level lies in the complementary piece. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasurableFunctionUP
  MeasurableFunctionBorel CountableOrderIntervals ExtendedRealOrderTopology TopologicalBorel
  MeasurableSeparationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_function_level_separated]: direct forward
    direction of Federer 2.3.2(7), p. 74 It applies to every test set,
    including sets of infinite measure. *)
Theorem measurable_function_level_separated (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_level_separated mu f.
Proof.
move=> hf T a b hab.
have hA : measure_measurable mu (partial_function_preimage f [set y | y <= a%:E]).
  apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hm f hf).
  apply: closed_borel_set; exact: order_closed_lower_ray_closed.
rewrite (hA T); apply: leeD; first exact: lexx.
apply: (@measure_mono R X mu hm)=> x [hx [y [hy hby]]]; split=> //.
move=> [z [hz hza]].
have he : y = z := partial_function_single_valued hy hz.
have hba : b%:E <= a%:E by apply: le_trans hby _; by rewrite he.
have habE : a%:E < b%:E by rewrite lte_fin.
have hbad := lt_le_trans habE hba; by rewrite ltxx in hbad.
Qed.
