(** Federer (1969), 2.5.12, printed pp. 102–106: public representation
    theorem, almost uniqueness, and the measurable-function consequences.
    The chosen density is used only through the sealed laws. The local
    erratum has no correction to pp. 103–106. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower
  MeasureUP MeasureAlmostUP MeasureIntegralUP MeasurableFunctionUP SummableRealFunctionUP
  FunctionLatticeUP RealIntegralFunctionalUP FunctionLatticeRegularityUP
  VectorDaniellHypotheses VectorDaniellRepresentationUP VectorDaniellNormalisationUP
  VectorDaniellRepresentationSealed VectorDaniellRationalSpan VectorDaniellDensities
  VectorDaniellVariationIntegral VectorDaniellUniqueness VectorDaniellPairingConclusion
  PartialDualPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_daniell_representation]: the normalised
    density asserted by Federer 2.5.12, p. 103, for the
    regular measure representing the variation integral. *)
Theorem vector_daniell_representation (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (hL : is_function_lattice L) (hseries : has_lattice_unit_series L)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN L Q)
    (hT : is_vector_variation_functional N L Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice L)
      (variation_integral N Q T))
    (hreg : is_function_lattice_regular (positive_function_lattice L) phi) :
  exists k : X -> weak_dual_space hN, is_normalised_vector_daniell_density phi Q T k.
Proof.
exists (@VectorDaniellRepresentation.value R X E N hN hsep L Q T hL hseries hQ hM hT phi hphi hrep hreg).
exact (@VectorDaniellRepresentation.laws R X E N hN hsep L Q T hL hseries hQ hM hT phi hphi hrep hreg).
Qed.

(** Source for [vector_variation_representation]: the complete
    existence conclusion from hypotheses (1)–(5) in Federer
    2.5.12, pp. 102–103. The variation measure and its
    density are both produced; a representing measure is not
    an additional hypothesis. *)
Theorem vector_variation_representation (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R) :
  is_function_lattice L -> has_lattice_unit_series L ->
  is_vector_function_space Q -> is_vector_lattice_module hN L Q ->
  is_vector_variation_functional N L Q T ->
  exists phi : set X -> \bar R, exists k : X -> weak_dual_space hN,
    is_measure phi /\
    is_real_integral_functional phi (positive_function_lattice L) (variation_integral N Q T) /\
    is_function_lattice_regular (positive_function_lattice L) phi /\
    is_normalised_vector_daniell_density phi Q T k.
Proof.
move=> hL hseries hQ hM hT.
have hnon : exists f, L f.
  exists (fun x => N (0 : E)).
  exact (@vector_lattice_module_norm R X E N hN L Q hM (fun _ => 0)
    (vector_function_space_zero hQ)).
have [phi [hphi [hrep [hreg _]]]] :=
  @variation_measure_exists R X E N hN L Q T hL hQ hM hT hnon.
have [k hk] := @vector_daniell_representation R X E N hN hsep L Q T
  hL hseries hQ hM hT phi hphi hrep hreg.
exists phi,k; by split=> //; split=> //; split.
Qed.

(** Source for [vector_daniell_representation_almost_unique]:
    the almost-uniqueness assertion of Federer 2.5.12, p. 103.
    Competing densities need only be weakly measurable and
    represent T; no norm bound is imposed on them. *)
Theorem vector_daniell_representation_almost_unique (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (k l : X -> weak_dual_space hN) :
  is_function_lattice L -> has_lattice_unit_series L ->
  is_vector_lattice_module hN L Q ->
  is_real_integral_functional phi (positive_function_lattice L) (variation_integral N Q T) ->
  is_function_lattice_regular (positive_function_lattice L) phi ->
  is_vector_daniell_density phi Q T k -> is_vector_daniell_density phi Q T l ->
  measure_almost_everywhere phi [set x | k x=l x].
Proof.
move=> hL hseries hM hrep hreg hk hl.
have [D hD] := @rational_dense_subspace_exists R E N hN hsep.
have hX := @variation_space_countably_measurable R X E N L Q T phi hphi hrep hseries.
exact (@vector_daniell_density_almost_unique R X E N hN L Q T phi hphi D hD
  k l hL hM hrep hreg hX hk hl).
Qed.

(** Source for [vector_daniell_measurable_members]: every
    member of Q is measurable, Federer 2.5.12, p. 103,
    proved on p. 104 by a countable norming family. *)
Theorem vector_daniell_measurable_members (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (phi : set X -> \bar R) (hphi : is_measure phi) :
  is_function_lattice L -> is_vector_lattice_module hN L Q ->
  is_real_integral_functional phi (positive_function_lattice L) (variation_integral N Q T) ->
  forall w, Q w -> is_measure_measurable_function phi
    (partial_function_total (w : X -> real_norm_metric_space hN)).
Proof.
move=> hL hM hrep w hw.
have [D hD] := @rational_dense_subspace_exists R E N hN hsep.
exact (@vector_member_measurable R X E N hN L Q T hL hM phi hphi hrep D hD w hw).
Qed.

(** Source for [vector_daniell_pairing_consequences]: the final
    two sentences of Federer 2.5.12, p. 103. Partial
    measurable eta is allowed. Summability of nu o eta
    implies summability of <eta,k>, with the unit-norm bound
    on its integral proved on p. 105. *)
Theorem vector_daniell_pairing_consequences (R : realType) (X : choiceType)
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
    exists c : R, is_measure_integral phi (partial_dual_pairing k eta) c%:E /\ Num.norm c <= a).
Proof.
move=> hk heta.
exact (@partial_dual_pairing_measurable_summable R X E N hN hsep phi hphi k eta
  (vector_daniell_density_measurable (normalised_vector_density_laws hk))
  (normalised_vector_density_bound hk) heta).
Qed.
