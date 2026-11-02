(** The sets P^n in Federer (1969), 2.9.7, p. 156, and their covering of A
    outside Z and the corrected W. Measurability follows from 2.9.6;
    half-open geometric cells are disjoint. Federer's erratum, p. 3, book p.
    155 line 26, replaces infinite values alone by non-real values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  PartialFunctionUP MeasureDerivationContext MeasureDerivates DerivationMeasurable
  DerivationLevelSeparation GeometricFunctionBands GeometricIntegerCells DerivationZeroAndNonreal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_geometric_cell]: direct P^n
    in Federer 2.9.7, p. 156: intersect
    A with t^n<=D<t^(n+1), for an integer n.
    Zero, infinite and undefined values are excluded. *)
Definition derivation_geometric_cell (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop)
    (A : set X) (t : R) (j : int) :=
  A `&` geometric_function_band (measure_derivate psi phi V) t j.

(** Source for [derivation_geometric_cell_measurable]: the
    phi measurability of P^n in Federer 2.9.7,
    p. 156, derived from 2.9.6 and
    measurability of the target A. *)
Lemma derivation_geometric_cell_measurable (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A t j :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_measurable phi A -> measure_measurable phi (derivation_geometric_cell psi phi V A t j).
Proof.
move=> hc hp hA; have hm := derivation_measure_law (derivation_context_measure hc).
apply: (@measure_measurable_intersection R X phi hm A _ hA).
exact (@geometric_function_band_measurable R X phi (measure_derivate psi phi V) t j hm
  (@federer_2_9_6 R X phi psi V hc hp)).
Qed.

(** Source for [derivation_geometric_cells_disjoint]: the
    disjointness assertion in Federer 2.9.7, p. 156,
    with the same closed-lower, open-upper convention. *)
Lemma derivation_geometric_cells_disjoint (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) A (t : R) :
  (1<t)%R -> forall i j, i<>j ->
    derivation_geometric_cell psi phi V A t i `&` derivation_geometric_cell psi phi V A t j=set0.
Proof.
move=> ht i j hne; apply/seteqP; split=> [x [[_ hi] [_ hj]]|x []].
exfalso; apply: hne; exact: geometric_function_band_disjoint ht hi hj.
Qed.

(** Source for [derivation_geometric_remainder_subset]: the
    exhaustion of A outside Z and W in Federer
    2.9.7, p. 156. W uses the
    corrected non-real-value condition, including points
    outside the partial derivative domain. *)
Lemma derivation_geometric_remainder_subset (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A (t : R) :
  is_measure phi -> is_measure psi -> (1<t)%R ->
  (A `\` \bigcup_j derivation_geometric_cell psi phi V A t j) `<=`
    derivation_zero_points psi phi V `|` derivation_nonreal_points psi phi V.
Proof.
move=> hf hp ht x [hx hn].
case: (pselect (exists r : R, partial_function_graph (measure_derivate psi phi V) x r%:E))=> [[r hr]|hnr].
- case: (eqVneq r 0%R)=> [hr0|hr0].
  + left; by move: hr; rewrite hr0.
  + have hrpos := @measure_derivate_value_nonnegative R X phi psi V x r%:E hf hp hr.
    rewrite lee_fin in hrpos.
    have hrp : (0<r)%R by rewrite lt_def hr0 hrpos.
    have [j [hlo hhi]] := @geometric_integer_cell_exists R t r ht hrp.
    exfalso; apply: hn; exists j; first exact I.
    split; first exact hx.
    exists r%:E; split; first exact hr.
    split; [by rewrite lee_fin|by rewrite lte_fin].
- by right.
Qed.

(** Source for [derivation_geometric_remainder_null]: supporting
    deletion of Z and W before the two sums in
    Federer 2.9.7, p. 156. Apply this
    to psi_phi and to the integral-density measure;
    neither target boundedness nor finite totals are needed. *)
Lemma derivation_geometric_remainder_null (R : realType) (X : metricType R)
    (phi psi mu : set X -> \bar R) (V : X -> set X -> Prop) A (t : R) :
  is_measure phi -> is_measure psi -> is_measure mu -> (1<t)%R ->
  mu (derivation_zero_points psi phi V)=0 -> mu (derivation_nonreal_points psi phi V)=0 ->
  mu (A `\` \bigcup_j derivation_geometric_cell psi phi V A t j)=0.
Proof.
move=> hf hp hm ht hZ hW.
apply: (@measure_null_subset R X mu hm _ (derivation_zero_points psi phi V `|` derivation_nonreal_points psi phi V)).
- exact (@derivation_geometric_remainder_subset R X phi psi V A t hf hp ht).
- exact (@measure_null_union R X mu hm _ _ hZ hW).
Qed.
