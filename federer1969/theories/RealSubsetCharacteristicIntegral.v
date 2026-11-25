(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension MeasureSubsetIntegral
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_subset_characteristic_integral]: supporting
    characteristic-test identity for the comparison with 2.9.7
    in Federer 2.9.10, p. 157. Multiplication by an abstract
    characteristic function equals the zero extension defining
    the subset integral (2.4.10, p. 85); all values are finite. *)
Lemma real_subset_characteristic_integral (R : realType) (X : choiceType)
    (phi : set X -> \bar R) A (s k : X -> R) c :
  is_characteristic_function A s ->
  (is_measure_subset_integral phi A (real_total_integrand k) c <->
    is_measure_integral phi (real_total_integrand (fun x => (s x*k x)%R)) c).
Proof.
move=> hs.
have he x y : partial_function_graph
    (partial_function_zero_extension (0 : extended_real_line R) A (real_total_integrand k)) x y <->
    partial_function_graph (real_total_integrand (fun x => (s x*k x)%R)) x y.
  case: (pselect (A x))=> hx.
  - rewrite (@partial_function_zero_extension_on X (extended_real_line R) 0 A
      (real_total_integrand k) x y hx) !real_total_integrand_graph /=.
    by rewrite (characteristic_on_set hs hx) mul1r.
  - rewrite (@partial_function_zero_extension_off X (extended_real_line R) 0 A
      (real_total_integrand k) x y hx) real_total_integrand_graph /=.
    rewrite (characteristic_off_set hs hx) mul0r; split; move=> hy; symmetry; exact hy.

split; [exact: measure_integral_graph_equivalent he|exact: measure_integral_graph_equivalent (fun x y => iff_sym (he x y))].
Qed.
