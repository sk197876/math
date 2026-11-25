(** The distance to the total zero function in Federer (1969), 2.3.8, p. 78.
    This supporting identity is used for the characteristic-function
    convergence counterexample. Source context and partial-domain
    convention: MeasureConvergenceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureGauge MeasureNullModification MeasureConvergenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_total_distance_zero]: the pseudodistance
    from a total function to zero equals its gauge, by the
    definition in Federer 2.3.8, p. 78. *)
Lemma measure_total_distance_zero (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : V -> R) (f : X -> V) :
  measure_normed_distance mu N (partial_function_total f) (partial_function_total (fun _ => 0%R)) =
    measure_gauge mu N (partial_function_total f).
Proof.
apply: (@measure_gauge_almost_invariance R X V mu hm N).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
move=> x _; exists (f x); split=> //.
apply/partial_vector_subtract_graph; exists (f x), (0%R : V); split=> //; split=> //.
by rewrite subr0.
Qed.
