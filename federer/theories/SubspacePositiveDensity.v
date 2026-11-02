(** Federer (1969), 2.6.4, pp. 118–119: the nonnegative summable-function
    reduction for tensor-image density, using the finite simple minorants of
    2.4.6, p. 84. Here only linear-subspace laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra finmap functions classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialAbsolutePartsGraph
  PartialExtendedArithmetic PartialExtendedOrderLoci ModuleQuotient
  SummableRealFunctionUP SubspaceLoneApproximationUP SubspaceSimpleDensity
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

(** Source for [subspace_nonnegative_summable_density]: supporting
    passage from finite simple functions to nonnegative summable
    functions in Federer 2.6.4, pp. 118–119. The proof
    retains partial domains and almost-everywhere nonnegativity. *)
Theorem subspace_nonnegative_summable_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (L : subspace (GRing.Lmodule.clone R (X -> R^o) _))
    (hLs : forall f, L f -> summable_real_functions mu f)
    (hchar : forall (A : set X) (s : X -> R), measure_measurable mu A ->
      mu A < +oo -> is_characteristic_function A s -> is_subspace_lone_approximable mu L s)
    (f : partial_function X (extended_real_line R)) (d : R) :
  is_measure_summable mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> (0 < d)%R ->
  exists (h : X -> R) (q : R), L h /\
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
have hua := @subspace_finite_positive_simple_density R X R mu hm L hLs hchar C A s (fun y => y)
  (fun y _ => hs y) hC.1 hfin (fun y hy => ltW (hC.2.2.1 y hy)).
have [h [e [hh [he hed]]]] := hua.2 _ hd2.
have hhs : summable_real_functions mu h := @hLs h hh.
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
