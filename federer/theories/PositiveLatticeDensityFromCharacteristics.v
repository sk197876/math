(** Federer (1969), 2.5.14, p. 108: supporting positive density for the
    Radon vector representation. This isolates the finite-sum step of 2.5.3,
    p. 95, from any particular measure envelope. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialAbsolutePartsGraph
  PartialExtendedArithmetic PartialExtendedOrderLoci FunctionLatticeUP
  RealIntegralFunctionalUP SummableRealFunctionUP LatticeL1ApproximationUP PositiveCharacteristicDensity
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

(** Source for [positive_lattice_density_from_characteristics]:
    the finite-simple reduction of Federer 2.5.3, p. 95,
    supporting the Radon variant in 2.5.14, p. 108.
    This consequence of characteristic approximation retains
    partial domains and almost-everywhere nonnegativity. *)
Theorem positive_lattice_density_from_characteristics (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hL0 : L (fun _ => 0%R))
    (hchar : forall S s, is_characteristic_function S s -> measure_measurable mu S -> mu S < +oo ->
      is_positive_lattice_l1_approximable mu L s)
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
have hua := @positive_characteristic_finite_simple_density R X R L F hL mu hm hF hL0 hchar C A s (fun y => y)
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
