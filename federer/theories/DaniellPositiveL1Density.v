(** Federer (1969), 2.5.3, p. 94, second further condition, proof p. 95:
    nonnegative summable functions are approximated by L+ in integral
    absolute error. Here the finite-simple supremum underlying 2.4.6
    supplies the last reduction in Federer's proof. We prove the arbitrary
    positive epsilon bound, and then the printed 4 delta bound. Partial
    domains and almost-everywhere nonnegativity are retained, including
    infinite values on null sets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialAbsolutePartsGraph
  PartialExtendedArithmetic PartialExtendedOrderLoci FunctionLatticeUP DaniellCoverUP
  RealIntegralFunctionalUP SummableRealFunctionUP LatticeL1ApproximationUP DaniellFiniteSimpleDensity
  FinitePositiveSimpleIntegralSupremum FinitePositiveSimpleApproximation PartialSimpleIntegralError
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureFiniteCharacteristicIntegral MeasureFiniteSimpleComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_nonnegative_summable_lattice_density]: complete
    second further condition of Federer 2.5.3, p. 94, proof p. 95 Arbitrary
    epsilon is equivalent to the printed 4 delta by rescaling. The
    conclusion provides both summability and the actual finite integral of
    the error. *)
Theorem daniell_nonnegative_summable_lattice_density (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hc : is_daniell_cover_envelope L F mu)
    (f : partial_function X (extended_real_line R)) (d : R) :
  is_measure_summable mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> (0 < d)%R ->
  exists (h : X -> R) (q : R), positive_function_lattice L h /\
    is_measure_integral mu
      (partial_extended_function_absolute_value (partial_extended_function_subtract (real_total_integrand h) f)) q%:E /\
    (q < d)%R.
Proof.
move=> [a hi] hp hd; have hd2 : (0 < d/2)%R by rewrite divr_gt0 // ltr0n.
have [C [A [b [hC [hfin [hsum hab]]]]]] :=
  @finite_positive_simple_integral_approximation R X mu hm f a (d/2)%R hp hi hd2.
pose s y := @CharacteristicFunction.value R X (A y).
have hs y : is_characteristic_function (A y) (s y) := @CharacteristicFunction.laws R X (A y).
pose u x := (\sum_(y <- C) y*s y x)%R.
have hui : is_measure_integral mu (real_total_integrand u) b%:E.
  have hu := @measure_finite_positive_characteristic_integral R X R mu hm C A s (fun y => y)
    (fun y _ => hs y) hC.1 hC.2.2.1.
  by rewrite hsum in hu.
have hua := @daniell_finite_positive_simple_density R X R L F hL mu hm hF hc C A s (fun y => y)
  (fun y _ => hs y) hC.1 hfin (fun y hy => ltW (hC.2.2.1 y hy)).
have [h [e [hh [he hed]]]] := hua.2 _ hd2.
have hhs : summable_real_functions mu h by exists (F h); exact: hF h hh.1.
have horder : measure_almost_everywhere mu (partial_extended_le_locus (real_total_integrand u) f).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp)=> x [z [hz hz0]].
  exists (u x)%:E,z; split; first by apply/real_total_integrand_graph.
  split=> //; apply: (@finite_disjoint_characteristic_bound R X R C A s (fun y => y) x z
    (fun y _ => hs y) hC.2.1 hz0)=> y hy hxy.
  have [v [hv hyv]] := hC.2.2.2 y hy x hxy.
  have hvz : v=z := partial_function_single_valued hv hz; by rewrite -hvz.
have [q [hq hqbound]] := @partial_simple_integral_error_transfer R X mu hm f h u a b e hi hui hhs he horder.
exists h,q; split=> //; split=> //.
have habd : (a-b < d/2)%R.
  have hl := (andP hab).1; by move: hl; rewrite ltrBlDr addrC -ltrBlDr.
have hsumd := ltrD hed habd.
rewrite -splitr in hsumd; exact: le_lt_trans hqbound hsumd.
Qed.

(** Source for [daniell_nonnegative_summable_four_delta]: printed error
    bound integral |k-u| < 4 delta in Federer 2.5.3, p. 94 *)
Corollary daniell_nonnegative_summable_four_delta (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hc : is_daniell_cover_envelope L F mu)
    (f : partial_function X (extended_real_line R)) (d : R) :
  is_measure_summable mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> (0 < d)%R ->
  exists (h : X -> R) (q : R), positive_function_lattice L h /\
    is_measure_integral mu
      (partial_extended_function_absolute_value (partial_extended_function_subtract (real_total_integrand h) f)) q%:E /\
    (q < 4*d)%R.
Proof.
move=> hf hp hd; have h4 : (0 < 4*d)%R by rewrite mulr_gt0 // ltr0n.
exact: (@daniell_nonnegative_summable_lattice_density R X L F hL mu hm hF hc f (4*d)%R hf hp h4).
Qed.
