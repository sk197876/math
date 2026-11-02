(** Federer (1969), 2.5.3, p. 94: finite decreasing intersections of
    increasing level unions. These consequences retain the first set's
    finiteness hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability
  RealIntegralFunctionalUP MeasureUP MeasureBasic MeasureCountableClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_finite_hull_measurable]: measurability
    of F2 in Federer 2.5.3, p. 94 No L regularity assumption is needed for
    this countable-intersection consequence. *)
Lemma represented_lattice_finite_hull_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A) (S : set X) :
  function_lattice_finite_hulls L mu S -> measure_measurable mu S.
Proof.
move=> [V [hV [_ [_ ->]]]].
apply: (@measure_measurable_countable_intersection R X nat mu hm setT V (countableP _))=> n _.
exact: (@represented_lattice_increasing_level_measurable R X L A mu hm hA (V n) (hV n)).
Qed.

(** Source for [function_lattice_finite_hull_finite]: F2 sets have finite
    measure by containment in the first set; supporting Federer 2.5.3, p.
    94. Measurability is not needed for this bound. *)
Lemma function_lattice_finite_hull_finite (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu : set X -> \bar R) (hm : is_measure mu) (S : set X) :
  function_lattice_finite_hulls L mu S -> mu S < +oo.
Proof.
move=> [V [_ [_ [hfin ->]]]].
apply: le_lt_trans (_ : mu (V 0%N) < +oo)=> //.
apply: (@measure_mono R X mu hm (\bigcap_n V n) (V 0%N))=> x hx.
exact: (hx 0%N Logic.I).
Qed.

(** Source for [function_lattice_finite_hulls_measure_independent]: F2 is
    independent of the representing measure once their restrictions to F1
    agree, as asserted in Federer 2.5.3, p. 94 This isolates the
    finite-first-set condition in that conclusion. *)
Lemma function_lattice_finite_hulls_measure_independent (R : realType) (X : Type)
    (L : set (X -> R)) (mu nu : set X -> \bar R) :
  (forall S, function_lattice_increasing_levels L S -> mu S=nu S) ->
  function_lattice_finite_hulls L mu = function_lattice_finite_hulls L nu.
Proof.
move=> heq; apply/seteqP; split=> S [V [hV [hmono [hfin hS]]]];
  exists V; split=> //; split=> //; split=> //.
- by rewrite -(heq _ (hV 0%N)).
- by rewrite (heq _ (hV 0%N)).
Qed.
