(** Federer (1969), 2.5.3, proof p. 95: first approximate the characteristic
    function a of a finite measurable set by h in L+. Here, following
    Federer, we use min(h_n,a) for a sequence suiting the set, and
    increasing convergence; the resulting integral identity is equivalent to
    Federer's positive/negative part calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellCoverUP DaniellCoverBasic DaniellSupportedMinorant
  RealIntegralFunctionalUP RealIntegralFunctionalSealed RealIntegralIncreasingContinuity
  RealIntegralAbsoluteMinimum SummableRealFunctionUP SummableRealArithmetic
  CharacteristicFunctionUP MeasureIntegralUP MeasureUP MeasureBasic MeasureCharacteristicIntegral ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_characteristic_lattice_approximation]:
    characteristic-function case of the second further condition of Federer
    2.5.3, p. 94, proved on p. 95 The integral error is strictly below 3
    delta, so also below the printed 4 delta. *)
Theorem daniell_characteristic_lattice_approximation (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hc : is_daniell_cover_envelope L F mu) (S : set X) (s : X -> R) (d : R) :
  is_characteristic_function S s -> measure_measurable mu S -> mu S < +oo -> (0 < d)%R ->
  exists (h : X -> R) (e : R), positive_function_lattice L h /\
    is_measure_integral mu (real_total_integrand (fun x => `|h x-s x|%R)) e%:E /\
    (e < d+(d+d))%R.
Proof.
move=> hs hS hfin hd.
have hSf : mu S \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm S).
pose a := fine (mu S).
have hsi : is_measure_integral mu (real_total_integrand s) a%:E.
  rewrite /a fineK //; exact: (@measure_characteristic_integral R X mu hm S s hs hS).
have hss : summable_real_functions mu s by exists a.
have ha : mu S < (a+d)%R%:E by rewrite -(fineK hSf) lte_fin /a ltrDl.
have [f [c [hf [hcost hcb]]]] := daniell_cover_approximation hc ha.
pose g n x := Order.min (f n x) (s x).
have hgs n : summable_real_functions mu (g n).
  apply: (@summable_real_minimum R X mu hm (f n) s)=> //.
  exists (F (f n)); exact: hF _ (hf.1 n).1.
pose J := @RealIntegralFunctional.value R X mu (summable_real_functions mu) (fun _ h => h).
have hJ := @RealIntegralFunctional.laws R X mu (summable_real_functions mu) (fun _ h => h).
have hgi n := hJ (g n) (hgs n).
have hsp : function_nonnegative s.
  move=> x; case: (pselect (S x))=> hx.
  - by rewrite (characteristic_on_set hs hx) ler01.
  - by rewrite (characteristic_off_set hs hx).
have hsb x : S x -> (s x <= 1)%R by move=> hx; rewrite (characteristic_on_set hs hx).
have hinc := @daniell_suiting_minimum_increases R X L S f s hf hsp hsb
  (fun x hx => characteristic_off_set hs hx).
have hlim := @real_integral_increasing_continuity R X mu hm g s (fun n => J (g n)) a hgi hsi hinc.
have hl : (a-d)%R%:E < a%:E by rewrite lte_fin ltrBlDl ltrDr.
have [N hN] := hlim.2.1 _ hl.
have hJN : (a-d < J (g N))%R by have hh := hN N (leqnn N); move: hh; rewrite lte_fin.
have hFN : (F (f N) < a+d)%R.
  have hub : (F (f N))%:E <= c by apply: (extended_real_supremum_upper hcost); exists N.
  have hh := le_lt_trans hub hcb; by move: hh; rewrite lte_fin.
pose e := (F (f N)+a-2*J (g N))%R.
exists (f N),e; split; first exact: hf.1 N.
split.
- exact: (@real_total_integral_absolute_difference_minimum R X mu hm (f N) s (F (f N)) a (J (g N))
    (hF _ (hf.1 N).1) hsi (hgi N)).
- have hb : (e < (a+d)+a-2*(a-d))%R.
    rewrite /e; apply: ltrD.
    + by rewrite ltrD2r.
    + by rewrite ltrN2 ltr_pM2l // ltr0n.
  have he : ((a+d)+a-2*(a-d))%R=(d+(d+d))%R.
    rewrite mulrBr opprB !mulr_natl !mulr2n [(a+d+a)%R]addrAC addrA.
    by rewrite -[(a+a+d+(d+d))%R]addrA [(a+a+(d+(d+d)))%R]addrC addrK.
  by rewrite he in hb.
Qed.
