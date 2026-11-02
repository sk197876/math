(** Public density measure for Federer (1969), 2.4.10, p. 85, using only its
    sealed defining formula. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP PartialExtendedOrderLoci
  MeasureDensityUP MeasureDensitySealed MeasureDensityCover MeasureDensityMeasurable MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_with_density]: public set function
    psi of Federer 2.4.10, p. 85, through
    the abstract upper-integral specification. *)
Definition measure_with_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (h : partial_function X (extended_real_line R)) := MeasureDensity.value mu h.

(** Source for [measure_with_density_laws]: defining law
    of psi in Federer 2.4.10, p. 85. *)
Lemma measure_with_density_laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (h : partial_function X (extended_real_line R)) :
  is_measure_density mu h (measure_with_density mu h).
Proof. exact: MeasureDensity.laws. Qed.

(** Source for [measure_with_density_is_measure]: public
    measure assertion of Federer 2.4.10, p. 85,
    requiring nonnegativity almost everywhere but not measurability. *)
Theorem measure_with_density_is_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) -> is_measure (measure_with_density mu h).
Proof. exact (@measure_density_is_measure R X mu (measure_with_density mu h) hm h (measure_with_density_laws mu h)). Qed.

(** Source for [measure_with_density_measurable]: public
    measurable-set preservation in Federer 2.4.10, p. 85. *)
Theorem measure_with_density_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) (A : set X) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  measure_measurable mu A -> measure_measurable (measure_with_density mu h) A.
Proof. exact (@measure_density_preserves_measurable_sets R X mu (measure_with_density mu h) hm h A (measure_with_density_laws mu h)). Qed.
