(** Federer (1969), 2.5.5, pp. 96–97: complete representation of a Daniell
    integral by its positive and negative variation measures, including the
    all-L formula and the final lower-limit separation assertion. The
    nonempty-lattice hypothesis is made explicit: the printed closure-only
    definition allows an empty lattice, which has no regular hulls. This is
    a local boundary correction, separate from Federer's erratum No
    finite-total-measure or vector-space hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellVariationUP DaniellVariation
  DaniellVariationFunctionals DaniellVariationRepresentation DaniellVariationSeparation
  FunctionLatticeRegularityUP RealIntegralFunctionalUP SummableRealFunctionUP
  ExtendedLowerLimitUP MeasureUP MeasureIntegralUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_integral_representation]: all conclusions of Federer
    2.5.5, p. 96, with the proof on p. 97 The two variations are specified
    abstractly by the displayed supremum/infimum laws; the measures are L+
    regular, signed integrals exist for every f in L, and the separating
    function is the lower limit of a sequence in L+ below f, even at
    exceptional points. *)
Theorem daniell_integral_representation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_function_lattice L -> is_daniell_integral L A -> (exists f, L f) ->
  exists (P Q : (X -> R) -> R) (mu nu : set X -> \bar R),
    is_daniell_positive_variation L A P /\ is_daniell_negative_variation L A Q /\
    is_measure mu /\ is_measure nu /\
    is_function_lattice_regular (positive_function_lattice L) mu /\
    is_function_lattice_regular (positive_function_lattice L) nu /\
    is_real_integral_functional mu (positive_function_lattice L) P /\
    is_real_integral_functional nu (positive_function_lattice L) Q /\
    (forall f, L f -> exists a b : R,
      is_measure_integral mu (real_total_integrand f) a%:E /\
      is_measure_integral nu (real_total_integrand f) b%:E /\ A f=(a-b)%R) /\
    forall f, positive_function_lattice L f -> exists (k : nat -> X -> R) (h : X -> R),
      (forall n, lattice_positive_order_interval L f (k n)) /\
      (forall x, (0 <= h x <= f x)%R) /\
      (forall x, is_extended_lower_limit (fun n => (k n x)%:E) (h x)%:E) /\
      measure_almost_everywhere mu [set x | h x=f x] /\
      measure_almost_everywhere nu [set x | h x=0%R].
Proof.
move=> hL hA hne.
pose P := @daniell_positive_variation R X L A hL hA.
pose Q := @daniell_negative_variation R X L A hL hA.
have hP := @daniell_positive_variation_specification R X L A hL hA.
have hQ := @daniell_negative_variation_specification R X L A hL hA.
have [mu [nu [hm [hn [hr [hs [hi [hj hsig]]]]]]]] :=
  @daniell_variations_regular_representation R X L A P Q hL hA hP hQ hne.
exists P,Q,mu,nu; split; first exact: hP.
split; first exact: hQ.
split; first exact: hm.
split; first exact: hn.
split; first exact: hr.
split; first exact: hs.
split; first exact: hi.
split; first exact: hj.
split; first exact: hsig.
exact: (@daniell_variation_separating_lower_limit R X L A P Q hL hA hP hQ mu nu hm hn hi hj).
Qed.
