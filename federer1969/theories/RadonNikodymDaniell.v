(** Federer (1969), 2.5.8, p. 100: the Daniell form of the Radon–Nikodym
    theorem, corrected by erratum p. 2, book p. 100 lines 3 and 5. The
    total-domain space and null-norm annihilation are explicit; no
    sigma-finiteness or finite total mass is added. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP DaniellIntegralUP TotalScalarLpUP TotalScalarLpLattice
  FunctionOperatorSeminorm TotalScalarLpFiniteSeminorm LpFunctionalDensityUP
  LpLinearFunctionalRepresentation DaniellVectorLinearity LinfinityDaniellBounded.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_nikodym_daniell_representation]: complete corrected
    Federer 2.5.8, p. 100; erratum p. 2, lines 3 and 5 Exact norm and almost
    uniqueness are inherited from 2.5.7. *)
Theorem radon_nikodym_daniell_representation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : (X -> R) -> R) :
  is_daniell_integral (total_scalar_lp mu +oo) A ->
  (forall f, total_scalar_lp mu +oo f -> total_scalar_lp_norm mu +oo f=0 -> A f=0%R) ->
  exists k : X -> R, is_lp_functional_density mu +oo 1 A k /\
    total_scalar_lp_norm mu 1 k=function_operator_seminorm (total_scalar_lp mu +oo) A
      (finite_total_scalar_lp_norm mu +oo) /\
    forall l, is_lp_functional_density mu +oo 1 A l ->
      measure_almost_everywhere mu [set x | k x=l x].
Proof.
move=> hA hnull.
have hL := @total_scalar_lp_vector_lattice R X mu hm +oo (leey _).
have hlin := @vector_daniell_integral_linear R X _ A hL hA.
have hb := @linfinity_daniell_operator_finite R X mu hm A hA hnull.
apply: (@lp_linear_functional_representation R X mu hm +oo 1 A _ hlin hb _ _).2.
- by right; right.
- by [].
- move=> _; exact: (@daniell_integral_increasing_continuity R X _ A hA).
Qed.
