(** Federer (1969), 2.5.3, p. 94: the level families of any representing
    measure. These laws use actual integral witnesses, without assuming L
    regularity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies
  RealIntegralFunctionalUP SummableRealFunctionUP RealTotalCharacteristicBounds
  PartialFunctionUP ExtendedRealOrderTopology MeasurableFunctionBorel CountableOrderIntervals
  TopologicalBorel MeasureUP MeasureBasic MeasureCountableClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_strict_upper_level]: graph adapter for the first
    displayed level set in Federer 2.5.3, p. 94 *)
Lemma real_total_strict_upper_level (R : realType) (X : Type) (f : X -> R) t :
  partial_function_preimage (real_total_integrand f) [set y | t%:E < y]=
    [set x | (t < f x)%R].
Proof.
apply/seteqP; split.
- move=> x [y [hy ht]]; have he := (real_total_integrand_graph f x y).1 hy.
  change (is_true (t%:E < y)) in ht; change (is_true ((t < f x)%R)).
  by move: ht; rewrite -he lte_fin.
- move=> x hx; exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  change (is_true (t%:E < (f x)%:E)); by rewrite lte_fin.
Qed.

(** Source for [represented_lattice_strict_level_measurable]: measurability
    of F0 used in Federer 2.5.3, p. 94 Every representing measure has this
    property; regularity is not required. *)
Lemma represented_lattice_strict_level_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A) (S : set X) :
  function_lattice_strict_levels L S -> measure_measurable mu S.
Proof.
move=> [f [t [hf [ht ->]]]].
have hi := hA f hf.1.
rewrite -real_total_strict_upper_level.
apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hm _ hi.1).
apply: open_borel_set; exact: order_strict_upper_ray_open.
Qed.

(** Source for [represented_lattice_strict_level_bound]: the finite-measure
    estimate supporting positive strict levels in Federer 2.5.3, p. 94 *)
Lemma represented_lattice_strict_level_bound (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A) (f : X -> R) (t : R) :
  positive_function_lattice L f -> (0 < t)%R ->
  t%:E * mu [set x | (t < f x)%R] <= (A f)%:E.
Proof.
move=> hf ht.
have hS : function_lattice_strict_levels L [set x | (t < f x)%R].
  exists f,t; by split=> //; split.
have hmeas := @represented_lattice_strict_level_measurable R X L A mu hm hA _ hS.
apply: (@real_total_integral_level_lower_bound R X mu hm [set x | (t < f x)%R]
  f (A f)%:E t hmeas ht (hA f hf.1) hf.2)=> x hx.
exact: ltW hx.
Qed.

(** Source for [represented_lattice_strict_level_finite]: every F0 set has
    finite measure, supporting Federer 2.5.3, p. 94 The threshold's strict
    positivity is essential. *)
Lemma represented_lattice_strict_level_finite (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A) (S : set X) :
  function_lattice_strict_levels L S -> mu S < +oo.
Proof.
move=> [f [t [hf [ht ->]]]].
have hb := @represented_lattice_strict_level_bound R X L A mu hm hA f t hf ht.
case he: (mu [set x | (t < f x)%R])=> [r| |]; first exact: ltry.
- have htE : (0 : \bar R) < t%:E by rewrite lte_fin.
  by move: hb; rewrite he (gt0_muley htE) leye_eq.
- by rewrite ltNye.
Qed.

(** Source for [represented_lattice_increasing_level_measurable]:
    measurability of F1 used in Federer 2.5.3, p. 94 It follows from
    countable measurable unions. *)
Lemma represented_lattice_increasing_level_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A) (S : set X) :
  function_lattice_increasing_levels L S -> measure_measurable mu S.
Proof.
move=> [V [hV [_ ->]]].
apply: (@measure_measurable_sequence_union R X mu hm V)=> n.
exact: (@represented_lattice_strict_level_measurable R X L A mu hm hA (V n) (hV n)).
Qed.
