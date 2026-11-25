(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(12), p. 327:
    independent laws for an actual representative contained
    in every original holomorphic subvariety whose germ
    contains the given variety germ. Existence is proved
    separately by the finite stratification and holomorphic continuation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP SetGermOrder FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_minimal_representative]: every
    conclusion of 3.4.8(12), p. 327. The
    universal bound concerns actual holomorphic subvarieties
    on the original prescribed neighbourhood. *)
Record is_holomorphic_minimal_representative (R:realType) n
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0)
    (U S:set (coordinate_space (ComplexScalars.C R) n)):Prop:={
  (** Source for [holomorphic_minimal_representative_germ]: the
      selected set represents alpha, 3.4.8(12), p. 327. *)
  holomorphic_minimal_representative_germ:
    @set_germ (Topological.clone (real_norm_metric_space
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 S=alpha;
  (** Source for [holomorphic_minimal_representative_bound]: actual
      containment for every original holomorphic supergerm,
      3.4.8(12), p. 327. *)
  holomorphic_minimal_representative_bound:forall T:set (coordinate_space (ComplexScalars.C R) n),
    @is_finite_holomorphic_variety R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) U T ->
    set_germ_subset alpha (@set_germ (Topological.clone (real_norm_metric_space
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 T) ->S `<=` T
}.
