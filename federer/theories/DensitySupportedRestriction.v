(** Federer (1969), 3.2.6, pp. 245–246: the
    multiplicity density vanishes off the finite-length compact
    image of a containing interval. This supporting restriction
    law allows a finite reference measure on that image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureRestriction MeasureDensityUP MeasureSubsetIntegral RestrictedUpperIntegral MeasureBoundGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [supported_density_restricted_reference]:
    supporting finite-reference reduction for Federer 3.2.6,
    p. 245. If the density has its actual value zero
    off E, restricting the reference measure to E preserves
    the density specification on every test set. *)
Theorem supported_density_restricted_reference (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (h:partial_function X (extended_real_line R)) E:
  is_measure_density mu h nu -> measure_measurable mu E ->
  (forall x,~E x -> partial_function_graph h x 0) ->
  is_measure_density (measure_restrict mu E) h nu.
Proof.
move=>hNu hE hOff T.
rewrite (hNu T) /measure_subset_upper_integral
  (@restricted_upper_integral_zero_extension R X mu hm E
    (partial_function_zero_extension (0:extended_real_line R) T h) hE).
apply:measure_upper_integral_graph_equivalent=>x z.
case:(pselect (E x))=>hx.
- split=>hz.
  + exact ((@partial_function_zero_extension_on X (extended_real_line R) 0 E
      (partial_function_zero_extension (0:extended_real_line R) T h) x z hx).2 hz).
  + exact ((@partial_function_zero_extension_on X (extended_real_line R) 0 E
      (partial_function_zero_extension (0:extended_real_line R) T h) x z hx).1 hz).
- rewrite (@partial_function_zero_extension_off X (extended_real_line R) 0 E
    (partial_function_zero_extension (0:extended_real_line R) T h) x z hx).
  have hValue:partial_function_graph (partial_function_zero_extension (0:extended_real_line R) T h) x 0.
    case:(pselect (T x))=>hTx.
    + apply/partial_function_zero_extension_graph; left; split=>//; exact (hOff x hx).
    + apply/partial_function_zero_extension_graph; right; by split.
  split=>hz.
  + exact (esym (partial_function_single_valued hValue hz)).
  + by rewrite hz.
Qed.
