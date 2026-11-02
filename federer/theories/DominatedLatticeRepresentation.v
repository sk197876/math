(** Federer (1969), 2.5.9, p. 100: representation of a Daniell functional
    dominated by a monotone one. The measure is specified by its
    L-regularity and representation laws. The total-domain and
    positive-density corrections are erratum p. 2, book p. 100 lines 21–24. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP CountablyMeasurableUP FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP TotalScalarLpUP
  RealLatticeDensityUP DominatedLatticeDensityExistence RealLatticeDensityUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_lattice_integral_representation]:
    complete corrected Federer 2.5.9, p. 100.
    The density is measurable, has essential norm at most one, and
    is unique almost everywhere even among unbounded measurable
    competing densities. Its countably measurable support is also retained. *)
Theorem dominated_lattice_integral_representation (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  is_function_lattice_regular L mu -> measure_countably_measurable mu setT ->
  is_daniell_integral L A ->
  (forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) ->
  exists k : X -> R, is_real_lattice_density mu L A k /\
    total_scalar_lp mu +oo k /\ total_scalar_lp_norm mu +oo k <= 1 /\
    forall l, is_real_lattice_density mu L A l ->
      measure_almost_everywhere mu [set x | k x=l x].
Proof.
move=> hF hrep hr hX hA hb.
have [k [hk [hkm hnorm]]] := @dominated_lattice_density_exists R X L hL F A mu hm hF hrep hr hX hA hb.
exists k; split=> //; split=> //; split=> // l hl.
exact: (@real_lattice_density_almost_unique R X L hL F A mu hm k l hrep hr hX hk hl).
Qed.
