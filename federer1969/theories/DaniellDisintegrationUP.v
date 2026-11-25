(** Federer (1969), 2.5.20, p. 114: specifications of the integral
    decomposition and its support conclusion. The latter is stated
    separately so the formula alone is not mistaken for the entire numbered
    item. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportDaniellSupport
  DaniellIntegralUP DaniellSpaceWeakTopology PartialFunctionBasic
  MeasureIntegralUP SummableRealFunctionUP MeasurableFunctionUP MeasureAlmostUP
  MeasureUP RadonMeasureUP FunctionLatticeUP FunctionLatticeRegularityUP ProductFibreVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_daniell_integral_decomposition]: the first
    integral formula and measurability conclusion of Federer
    2.5.20, p. 114. The scalar pairings have genuine
    finite integrals; the support assertion is separate. *)
Record is_daniell_integral_decomposition (R : realType) (X Y : topologicalType)
    (phi : set X -> \bar R) (mu : ((X*Y) -> R) -> R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) : Prop := {
  (** Source for [daniell_decomposition_values]: values of k
      are Daniell integrals, Federer 2.5.20, p. 114. *)
  daniell_decomposition_values : forall x,
    is_daniell_integral (@compactly_supported_continuous_functions R Y) (k x);
  (** Source for [daniell_decomposition_measurable]: weak
      measurability of k, Federer 2.5.20, p. 114. *)
  daniell_decomposition_measurable :
    is_measure_measurable_function phi (partial_function_total k);
  (** Source for [daniell_decomposition_integral]: the first
      displayed decomposition formula, Federer 2.5.20, p. 114. *)
  daniell_decomposition_integral : forall f,
    compactly_supported_continuous_functions f ->
    is_measure_integral phi (real_total_integrand (fun x => k x (fun y => f (x,y)))) (mu f)%:E
}.

(** Source for [daniell_decomposition_support_property]: the
    assertion immediately following the first integral formula
    in Federer 2.5.20, p. 114: the support of k(x)
    lies in the fibre of the support of mu almost everywhere. *)
Definition daniell_decomposition_support_property (R : realType) (X Y : topologicalType)
    (phi : set X -> \bar R) (mu : ((X*Y) -> R) -> R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) :=
  measure_almost_everywhere phi [set x |
    compact_support_daniell_support (k x) `<=`
      [set y | compact_support_daniell_support mu (x,y)]].

(** Source for [is_daniell_disintegration]: the Radon
    measure, weakly measurable Daniell family, integral formula,
    and fibre support assertion in the first paragraph of
    Federer 2.5.20, p. 114. The variation specification
    retains the particular measure obtained from 2.5.12(5),
    p. 103, needed by the final graph-specialization claim. *)
Record is_daniell_disintegration (R : realType) (X Y : topologicalType)
    (mu : ((X*Y) -> R) -> R) (phi : set X -> \bar R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) : Prop := {
  (** Source for [daniell_disintegration_measure]: measure
      laws for Phi in Federer 2.5.20, p. 114. *)
  daniell_disintegration_measure : is_measure phi;
  (** Source for [daniell_disintegration_radon]: Radon
      qualification of Phi in Federer 2.5.20, p. 114. *)
  daniell_disintegration_radon : is_radon_measure phi;
  (** Source for [daniell_disintegration_regular]: K(X)
      regularity of the representing measure obtained from
      2.5.12 and used in Federer 2.5.20, p. 114. *)
  daniell_disintegration_regular :
    is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi;
  (** Source for [daniell_disintegration_formula]: weak
      measurability and the actual integral formula,
      Federer 2.5.20, p. 114. *)
  daniell_disintegration_formula : is_daniell_integral_decomposition phi mu k;
  (** Source for [daniell_disintegration_support]: the fibre
      support containment in Federer 2.5.20, p. 114. *)
  daniell_disintegration_support : daniell_decomposition_support_property phi mu k;
  (** Source for [daniell_disintegration_variation]: Phi
      represents lambda of T=mu o S, as specified in
      2.5.12(5), p. 103, and applied in Federer
      2.5.20, p. 114. This fixes the same measure
      for the final graph specialization. *)
  daniell_disintegration_variation : forall f,
    positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    exists a : R, is_measure_integral phi (real_total_integrand f) a%:E /\
      is_product_fibre_variation mu f a
}.
