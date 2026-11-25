(** Federer (1969), 2.5.14, p. 108: public Radon vector representation for
    the compact-support lattice. The unit-series hypothesis of 2.5.12(3) is
    absent and decreasing-sequence continuity is derived from compactness.
    Linearity and finite variation bounds remain explicit. Uniqueness is
    local, as stated in the book. Downstream use is through the opaque
    representing-density interface. Source context:
    OrderBoundedVectorFunctionalUP.v and RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower
  FunctionLatticeUP CompactSupportFunctionUP CompactSupportFunctionLattice
  VectorDaniellHypotheses VectorDaniellRepresentationUP VectorDaniellNormalisationUP
  MeasureUP MeasureIntegralUP MeasurableFunctionUP SummableRealFunctionUP RadonMeasureUP
  RealIntegralFunctionalUP OrderBoundedVectorFunctionalUP CompactSupportVectorContinuity
  CompactVectorVariationRadon RadonVectorRepresentationSealed RadonVectorUniqueness
  VectorDaniellRepresentation LocallyNullMeasureUP PartialDualPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_vector_representation]: the density
    conclusion of Federer 2.5.14, p. 108, for a Radon
    measure representing the variation. Unlike 2.5.12(3),
    pp. 102–103, no lattice unit series is required. *)
Theorem radon_vector_representation (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_order_bounded_vector_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T)) :
  exists k : X -> weak_dual_space hN, is_normalised_vector_daniell_density phi Q T k.
Proof.
have hV := @compact_support_vector_variation_functional R X E N hN Q T
  (radon_hausdorff hr) (radon_locally_compact hr) hQ hM hT.
exists (@RadonVectorRepresentation.value R X E N hN hsep Q T hQ hM hV phi hphi hrep hr).
exact (@RadonVectorRepresentation.laws R X E N hN hsep Q T hQ hM hV phi hphi hrep hr).
Qed.

(** Source for [radon_vector_variation_representation]: complete
    vector existence assertion of Federer 2.5.14, p. 108.
    Both the Radon variation measure and normalized dual density
    are produced from the stated data. Compactness establishes
    sequential continuity; it does not replace the linearity
    and finite bounds used in the displayed estimate. *)
Theorem radon_vector_variation_representation (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_vector_function_space Q ->
  is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q ->
  is_order_bounded_vector_functional N (@compactly_supported_continuous_functions R X) Q T ->
  exists phi : set X -> \bar R, exists k : X -> weak_dual_space hN,
    is_measure phi /\ is_radon_measure phi /\
    is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T) /\ is_normalised_vector_daniell_density phi Q T k.
Proof.
move=> hh hl hQ hM hT.
have [phi [hm [hr hrep]]] := @compact_vector_variation_radon_measure R X E N hN Q T hh hl hQ hM hT.
have [k hk] := @radon_vector_representation R X E N hN hsep Q T hQ hM hT phi hm hr hrep.
exists phi,k; by split=> //; split=> //; split.
Qed.

(** Source for [radon_vector_representation_locally_unique]:
    "only locally so" in Federer 2.5.14, p. 108,
    specifies uniqueness of the weakly measurable density.
    No pointwise norm bounds on the competitors are added. *)
Theorem radon_vector_representation_locally_unique (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (k l : X -> weak_dual_space hN) :
  is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q ->
  is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
    (variation_integral N Q T) ->
  is_vector_daniell_density phi Q T k -> is_vector_daniell_density phi Q T l ->
  measure_locally_almost_everywhere phi [set x | k x=l x].
Proof. exact (@radon_vector_density_locally_unique R X E N hN hsep Q T phi hphi hr k l). Qed.

(** Source for [radon_vector_measurable_members]: measurability
    of Q retained from Federer 2.5.12, p. 103, with
    the Radon measure substituted in 2.5.14, p. 108.
    This consequence needs neither the unit series nor a
    continuity hypothesis on T. *)
Theorem radon_vector_measurable_members (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (phi : set X -> \bar R) (hphi : is_measure phi) :
  is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q ->
  is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
    (variation_integral N Q T) ->
  forall w, Q w -> is_measure_measurable_function phi
    (partial_function_total (w : X -> real_norm_metric_space hN)).
Proof.
exact (@vector_daniell_measurable_members R X E N hN hsep
  (@compactly_supported_continuous_functions R X) Q T phi hphi
  (@compactly_supported_continuous_functions_lattice R X)).
Qed.

(** Source for [radon_vector_pairing_consequences]: measurable
    and summable pairings in the final sentences of Federer
    2.5.12, p. 103, retained with the Radon measure in
    2.5.14, p. 108. Partial vector maps are allowed. *)
Theorem radon_vector_pairing_consequences (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (k : X -> weak_dual_space hN)
    (eta : partial_function X (real_norm_metric_space hN)) :
  is_normalised_vector_daniell_density phi Q T k ->
  is_measure_measurable_function phi eta ->
  is_measure_measurable_function phi (partial_dual_pairing k eta) /\
  (forall a : R, is_measure_integral phi (partial_norm_power N 1 eta) a%:E ->
    exists c : R, is_measure_integral phi (partial_dual_pairing k eta) c%:E /\ Num.norm c<=a).
Proof. exact (@vector_daniell_pairing_consequences R X E N hN hsep phi hphi Q T k eta). Qed.
