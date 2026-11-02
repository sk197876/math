(** Federer (1969), 2.4.12, pp. 86-87: subadditivity of the finite-p
    seminorm on A, allowing positive infinity. The p>1 argument is 2.4.15,
    p. 89. This statement retains partial domains; the vector-space
    assertion separately uses the total-domain restriction prescribed by
    Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasurableNormedFunctionUP MeasureLpNorm MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureMinkowski MeasureLoneTriangle.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_norm_triangle]: complete finite-p
    subadditivity assertion in Federer 2.4.12, p. 87.
    Infinite input norms make the estimate immediate; finite input
    norms give Lp membership, allowing 2.4.15 or the p=1
    integral argument. No finite-measure hypothesis is used. *)
Theorem measure_lp_norm_triangle (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_lp_norm mu N p (partial_vector_add f g) <= measure_lp_norm mu N p f + measure_lp_norm mu N p g.
Proof.
move=> hp hf hg.
have hfnn := @measure_lp_norm_nonnegative R X V N hN mu p f hm hp hf.1.
have hgnn := @measure_lp_norm_nonnegative R X V N hN mu p g hm hp hg.1.
have [hff|hff] := ltP (measure_lp_norm mu N p f) +oo; last first.
  have hb := leeD hff hgnn; rewrite adde0 in hb; exact: le_trans (leey _) hb.
have [hgf|hgf] := ltP (measure_lp_norm mu N p g) +oo; last first.
  have hb := leeD hfnn hgf; rewrite add0e in hb; exact: le_trans (leey _) hb.
have hflp : is_measure_lp_function mu p f.
  split=> //; split=> //; split=> //.
  exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p f hp hf.1 hff).
have hglp : is_measure_lp_function mu p g.
  split=> //; split=> //; split=> //.
  exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p g hp hg.1 hgf).
have [hp1|hp1] := eqVneq p 1%R.
- rewrite hp1 in hflp hglp *; exact (@measure_lone_triangle R X V N hN mu hm f g hflp hglp).
have hpgt : (1 < p)%R by rewrite lt_neqAle eq_sym hp1 hp.
exact (@minkowski_inequality R X V N hN mu hm p f g hpgt hflp hglp).
Qed.
