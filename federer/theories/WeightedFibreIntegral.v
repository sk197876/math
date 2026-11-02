(** Federer (1969), 2.5.10, p. 101: the nonnegative fibre-sum formula,
    obtained from its characteristic-set case 2.10.10, p. 176, using 2.3.3,
    p. 76, and 2.4.8, p. 84. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralScaleLaw
  MeasureUpperIntegralScale TotalNonnegativeSeriesIntegral
  NonnegativeSum WeightedCharacteristicExpansionUP WeightedCharacteristicIntegral
  MappingMultiplicity FibreNonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_fibre_integral]: supporting
    characteristic-expansion proof of the integral identity
    in Federer 2.5.10, p. 101. The setwise
    multiplicity identity is required only for the
    countable expansion sets E_n, and the arbitrary
    fibre sums are interchanged by 2.1.1(10), p. 53. *)
Theorem weighted_fibre_integral (R : realType) (X Y : choiceType)
    (p : X -> Y) (nu : set X -> \bar R) (beta : set Y -> \bar R)
    (hn : is_measure nu) (hb : is_measure beta)
    (f : X -> extended_real_line R) (r : nat -> R)
    (E : nat -> set X) (s : nat -> X -> R) :
  (forall n, (0<r n)%R) -> is_weighted_characteristic_expansion nu f r E s ->
  (forall n, is_measure_integral beta (partial_function_total
    (fun y => (@mapping_multiplicity R X Y p (E n) y : extended_real_line R))) (nu (E n))) ->
  is_measure_integral beta (partial_function_total
    (fun y => (fibre_nonnegative_sum p f y : extended_real_line R)))
    (nonnegative_sum setT (fun n => (r n)%:E*nu (E n))).
Proof.
move=> hr he hE.
pose u n y := ((r n)%:E*@mapping_multiplicity R X Y p (E n) y : extended_real_line R).
have hu n y : 0<=u n y.
  apply: mule_ge0; last exact: mapping_multiplicity_nonnegative.
  rewrite lee_fin; exact: ltW (hr n).
have hi n : is_measure_integral beta (partial_function_total (u n)) ((r n)%:E*nu (E n)).
  have h := @measure_integral_positive_scale R Y beta hb (r n) _ _ (hr n) (hE n).
  apply: (@measure_integral_graph_equivalent R Y beta _ _ _ _ h)=> y z.
  split.
  - move=> [v [hv <-]]; by rewrite -(hv : @mapping_multiplicity R X Y p (E n) y=v).
  - move=> hz; exists (@mapping_multiplicity R X Y p (E n) y); by split.
have hsum := @total_nonnegative_series_integral R Y beta hb u
  (fun n => (r n)%:E*nu (E n)) hu hi.
apply: (@measure_integral_graph_equivalent R Y beta _ _ _ _ hsum)=> y z.
change (nonnegative_sum setT (fun n => u n y)=z <-> fibre_nonnegative_sum p f y=z).
rewrite (@fibre_characteristic_expansion_sum R X Y p f r E s
  (fun n => ltW (hr n)) (expansion_characteristic_laws he) (expansion_pointwise_sum he)).
by [].
Qed.
