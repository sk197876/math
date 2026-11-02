(** Supporting measurability transfer for Federer (1969), 2.5.11, p. 102,
    where the identity L_1(phi)=L is inferred "from 2.5.3" (erratum p. 2,
    book p. 102 line 12, reads the total space). Let phi be L regular in the
    sense of 2.5.3, p. 94, and let nu be a measure with nu <= phi on all
    sets for which the strict levels {x: f(x)>t}, f in L+, t>0, are nu
    measurable. Then the families F_1 and F_2 of 2.5.3 consist of nu
    measurable sets, and every phi measurable set with finite phi measure
    differs from its F_2 hull by a phi null, hence nu null, set; so it is nu
    measurable. The argument follows LatticeRegularMeasureTransfer.v, where
    equality on F_1 is assumed; here only domination is available. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeRegularityUP
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableClosure MeasureAlmostBasic
  FiniteMeasurableDifferenceValue BorelDominatedMeasureTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lattice_finite_hull_measurable]: the members of
    the family F_2 of Federer 2.5.3, p. 94, are measurable for
    every measure for which the strict levels of L+ are measurable;
    supporting lemma for the identity L_1(phi)=L in 2.5.11, p. 102. *)
Lemma lattice_finite_hull_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu nu : set X -> \bar R) (hn : is_measure nu) :
  (forall S, function_lattice_strict_levels L S -> measure_measurable nu S) ->
  forall W, function_lattice_finite_hulls L mu W -> measure_measurable nu W.
Proof.
move=> hlev W [V [hV [_ [_ ->]]]].
apply: (@measure_measurable_countable_intersection R X nat nu hn setT V (countableP _))=> n _.
have [U [hU [_ ->]]] := hV n.
apply: (@measure_measurable_countable_union R X nat nu hn setT U (countableP _))=> j _.
exact: hlev _ (hU j).
Qed.

(** Source for [lattice_regular_dominated_finite_measurable]:
    supporting transfer of measurability for the identity
    L_1(phi)=L in Federer 2.5.11, p. 102. A phi measurable set S
    with finite phi measure has an F_2 hull W with phi(S)=phi(W) by
    2.5.3, p. 94; then phi(W~S)=0, so nu(W~S)=0 and S=W~(W~S) is nu
    measurable by 2.1.3, p. 55. *)
Theorem lattice_regular_dominated_finite_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu) :
  is_function_lattice_regular L mu -> (forall B, nu B <= mu B) ->
  (forall S, function_lattice_strict_levels L S -> measure_measurable nu S) ->
  forall S, measure_measurable mu S -> mu S < +oo -> measure_measurable nu S.
Proof.
move=> hr hd hlev S hS hfin.
have [W [hSW [hW [hval hWfin]]]] := (hr S).1 hfin.
have hWn := @lattice_finite_hull_measurable R X L mu nu hn hlev W hW.
have hz : mu (W `\` S) = 0.
  by rewrite (@finite_measurable_difference_value R X mu hm W S hS hSW hWfin) hval subrr.
have hzn := @dominated_measure_null R X mu nu hn hd _ hz.
have he : S = W `\` (W `\` S).
  apply/seteqP; split.
  - move=> x hx; split; first exact: hSW x hx.
    by move=> [_ hns]; exact: hns hx.
  - move=> x [hx hnS]; apply: contrapT=> hns; apply: hnS; by split.
rewrite he; exact (@measure_measurable_difference R X nu hn W (W `\` S) hWn (measure_null_measurable hn hzn)).
Qed.
