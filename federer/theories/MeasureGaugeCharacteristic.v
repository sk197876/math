(** Federer (1969), 2.3.8, p. 78, last displayed formula: the gauge of c
    times a characteristic function is min(c,mu(A)) for c nonnegative and
    finite. Source context: MeasureGauge.v. The numerical formula below
    needs no measurability of A; measurable A gives membership in the
    function space. Characteristic functions are used only through their
    abstract pointwise laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic ExtendedRealBounds MeasureGauge CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_gauge_two_value_norm]: supporting slightly
    more general form of the characteristic formula in Federer
    2.3.8, p. 78: a total map whose norm is c on A and
    zero elsewhere has gauge min(c,mu(A)). *)
Theorem measure_gauge_two_value_norm (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (h : X -> Y) (A : set X) (c : R) : (0 <= c)%R ->
  (forall x, A x -> N (h x) = c) -> (forall x, ~ A x -> N (h x) = 0%R) ->
  measure_gauge mu N (partial_function_total h) = Order.min c%:E (mu A).
Proof.
move=> hc hon hoff; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite le_min; apply/andP; split.
  + apply: measure_gauge_bound; split; first exact hc.
    have he : partial_norm_superlevel N (partial_function_total h) c%:E = set0.
      apply/seteqP; split; last by move=> x [].
      move=> x [y [<- hy]]; have hy' : (c < N (h x))%R := hy.
      case: (pselect (A x))=> hx.
      * by move: hy'; rewrite (hon x hx) ltxx.
      * move: hy'; rewrite (hoff x hx) ltNge hc; by [].
    by rewrite he (measure_empty hm).
  + apply: measure_gauge_bound; split; first exact: measure_nonnegative.
    apply: (@measure_mono R X mu hm)=> x [y [<- hy]].
    apply: contrapT=> hn.
    have hy' : mu A < (N (h x))%:E := hy.
    by move: hy'; rewrite (hoff x hn) ltNge (measure_nonnegative hm).
- apply: extended_real_inf_greatest=> r [hr hb].
  case: (leP c%:E r)=> hcr.
  + by rewrite ge_min hcr.
  + have har : mu A <= r.
      apply: le_trans _ hb; apply: (@measure_mono R X mu hm)=> x hx.
      exists (h x); split=> //.
      change (r < (N (h x))%:E); by rewrite (hon x hx).
    by rewrite ge_min har orbT.
Qed.

(** Source for [measure_gauge_scaled_characteristic]: direct
    characteristic-function formula in Federer 2.3.8, p. 78 The supplied
    function satisfies the characteristic laws, with no chosen
    implementation. *)
Theorem measure_gauge_scaled_characteristic (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> R) (c : R) : is_characteristic_function A s -> (0 <= c)%R ->
  measure_gauge mu (fun y : R => `|y|%R)
    (partial_function_total (fun x => (c*s x)%R)) = Order.min c%:E (mu A).
Proof.
move=> hs hc; apply: (@measure_gauge_two_value_norm R X R mu hm
  (fun y : R => `|y|%R) (fun x => (c*s x)%R) A c hc).
- move=> x hx; by rewrite (characteristic_on_set hs hx) mulr1 ger0_norm.
- move=> x hx; by rewrite (characteristic_off_set hs hx) mulr0 normr0.
Qed.
