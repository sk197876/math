(** Federer (1969), 2.5.5, pp. 96–97: the regular representing measures for
    the two variations, with the original functional represented by their
    difference. The nonempty-lattice premise is explicit: the proof assumes
    it, and an empty L+ has no regular hulls even for the empty set. This is
    a local boundary correction, not an entry in Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellVariationUP
  DaniellVariationFunctionals DaniellSignedVariationIntegral RegularDaniellRepresentation
  FunctionLatticeRegularityUP RealIntegralFunctionalUP SummableRealFunctionUP MeasureUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_variations_regular_representation]: measure
    existence and both integral representations in Federer 2.5.5, pp. 96–97
    The lower-limit separation postscript is a separate theorem. *)
Theorem daniell_variations_regular_representation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A P Q : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (hQ : is_daniell_negative_variation L A Q) :
  (exists f, L f) -> exists mu nu : set X -> \bar R,
    is_measure mu /\ is_measure nu /\
    is_function_lattice_regular (positive_function_lattice L) mu /\
    is_function_lattice_regular (positive_function_lattice L) nu /\
    is_real_integral_functional mu (positive_function_lattice L) P /\
    is_real_integral_functional nu (positive_function_lattice L) Q /\
    forall f, L f -> exists a b : R,
      is_measure_integral mu (real_total_integrand f) a%:E /\
      is_measure_integral nu (real_total_integrand f) b%:E /\ A f=(a-b)%R.
Proof.
move=> [f hf].
have hpos := @positive_function_lattice_laws R X L hL.
have hne : exists g, positive_function_lattice L g.
  exists (fun _ => 0%R); split; first exact: (@function_lattice_zero R X L hL f hf).
  by move=> x; exact: lexx.
have hPD := @positive_variation_monotone_daniell R X L A P hL hA hP.
have hQD := @negative_variation_monotone_daniell R X L A Q hL hA hQ.
have [mu [hm [hmu [hr _]]]] := @monotone_daniell_regular_representation R X _ P hpos hPD hne.
have [nu [hn [hnu [hs _]]]] := @monotone_daniell_regular_representation R X _ Q hpos hQD hne.
exists mu,nu; split; first exact: hm.
split; first exact: hn.
split; first exact: hr.
split; first exact: hs.
split; first exact: hmu.
split; first exact: hnu.
exact: (@daniell_signed_variation_integral R X L A P Q hL hA hP hQ mu nu hm hn hmu hnu).
Qed.
