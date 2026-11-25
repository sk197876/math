(** Federer (1969), 2.10.24, p. 187: pass from uniform pointwise generator
    bounds to Borel sets B_j. A finite equal-measure Borel hull preserves
    all measurable-generator intersection masses, by 2.1.4, p. 56. This
    makes the printed appeal to Borel regularity explicit, without assuming
    the pointwise good sets themselves Borel. Source context:
    WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureHull BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_hull_preserves_generator_bounds]: supporting
    Borel-hull step for B_j in 2.10.24,
    p. 187. A possibly nonmeasurable good
    subset H of finite-mass Borel A has a
    Borel hull inside A. Every eligible measurable generator
    inherits the same intersection bound, including
    those meeting the hull but missing H. *)
Theorem borel_hull_preserves_generator_bounds (R : realType) (X : topologicalType) (J : choiceType)
    (mu : set X -> \bar R) (S : J -> set X) (b : J -> \bar R) (P : set J) (A H : set X) :
  is_measure mu -> is_borel_regular_measure mu -> borel_set A -> mu A< +oo -> H `<=` A ->
  (forall j, measure_measurable mu (S j)) -> (forall j, 0<=b j) ->
  (forall j, P j -> (H `&` S j)!=set0 -> mu (A `&` S j)<=b j) ->
  exists B, borel_set B /\ H `<=` B /\ B `<=` A /\ mu B=mu H /\
    forall j, P j -> mu (B `&` S j)<=b j.
Proof.
move=> hm hr hA hAfin hHA hS hb hbound.
have [C [hHC [hC hval]]] := borel_regular_cover hr H.
pose B := C `&` A.
have hB : borel_set B := @borel_family_binary_intersection X setT (@borel_set X) (borel_sets_family X) C A hC hA.
have hHB : H `<=` B by move=> x hx; split; [exact: hHC|exact: hHA].
have hBA : B `<=` A by move=> x [_ hx].
have hBH : mu B=mu H.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite hval; apply: (@measure_mono R X mu hm)=> x [hx _]; exact hx.
  - exact: (@measure_mono R X mu hm H B hHB).
have hHfinite := le_lt_trans (@measure_mono R X mu hm H A hHA) hAfin.
have hBm := borel_regular_borel_measurable hm hr hB.
have hhull := @measure_hull_of_finite_equal_measure R X mu hm H B hHB hBm (esym hBH) hHfinite.
exists B; split=> //; split=> //; split=> //; split=> // j hjP.
have htest := @measure_hull_test R X mu H B hhull (S j) (hS j).
rewrite (setIC B (S j)) -htest (setIC (S j) H).
case: (pselect ((H `&` S j)!=set0))=> [hmeet|hempty].
- apply: le_trans _ (hbound j hjP hmeet); apply: (@measure_mono R X mu hm)=> x [hx hxS].
  split=> //; exact: hHA x hx.
- have he : H `&` S j=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  by rewrite he (measure_empty hm).
Qed.
