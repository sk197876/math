(** Federer (1969), 2.3.8, p. 78: the gauge triangle inequality. Source
    editions and partial- domain correction: MeasureGauge.v. This proof
    isolates the measure estimate from the separate closure-under-addition
    proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureBasic MeasureSplit MeasureGauge MeasureGaugeAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_sum_superlevel_cover]: direct inclusion behind the
    triangle inequality in Federer 2.3.8, p. 78 Extended thresholds are
    permitted, including positive infinity. *)
Lemma partial_sum_superlevel_cover (R : realType) (X : Type) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N)
    (f g : partial_function X V) r s :
  partial_norm_superlevel N (partial_vector_add f g) (r+s) `<=`
    partial_norm_superlevel N f r `|` partial_norm_superlevel N g s.
Proof.
move=> x [z [hz hlt]].
have [a [b [ha [hb he]]]] := proj1 (partial_vector_add_graph f g x z) hz.
rewrite he in hlt.
have [hra|hra] := boolP (r < (N a)%:E).
- left; exists a; by split.
have [hsb|hsb] := boolP (s < (N b)%:E).
- right; exists b; by split.
exfalso; have hra' : (N a)%:E <= r by rewrite leNgt.
have hsb' : (N b)%:E <= s by rewrite leNgt.
have ht : (N (a+b))%:E <= (N a)%:E + (N b)%:E.
  rewrite -EFinD lee_fin; exact: real_seminorm_triangle.
have hle := le_trans ht (leeD hra' hsb').
have hlt' : r+s < (N (a+b))%:E := hlt.
by move: hlt'; rewrite ltNge hle.
Qed.

(** Source for [measure_gauge_sum_feasible]: supporting feasible
    sum threshold in Federer 2.3.8, p. 78. Subadditivity
    applies without measurability of the exceptional sets. *)
Lemma measure_gauge_sum_feasible (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : V -> R)
    (hN : is_real_seminorm N) (f g : partial_function X V) r s :
  measure_gauge_feasible mu N f r -> measure_gauge_feasible mu N g s ->
  measure_gauge_feasible mu N (partial_vector_add f g) (r+s).
Proof.
move=> [hr hf] [hs hg]; split; first exact: adde_ge0 hr hs.
apply: le_trans (@measure_binary_cover R X mu hm _ _ _
  (@partial_sum_superlevel_cover R X V N hN f g r s)) _.
exact: leeD hf hg.
Qed.

(** Source for [measure_gauge_triangle]: direct triangle inequality of
    Federer 2.3.8, p. 78 Measurable superlevels suffice for attainment; the
    stronger function-space hypotheses are only needed for additive closure. *)
Theorem measure_gauge_triangle (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : V -> R)
    (hN : is_real_seminorm N) (f g : partial_function X V) :
  (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
  (forall t : R, measure_measurable mu (partial_norm_superlevel N g t%:E)) ->
  measure_gauge mu N (partial_vector_add f g) <= measure_gauge mu N f + measure_gauge mu N g.
Proof.
move=> hf hg; apply: measure_gauge_bound.
exact (@measure_gauge_sum_feasible R X V mu hm N hN f g _ _
  (@measure_gauge_attained R X V mu hm N f hf)
  (@measure_gauge_attained R X V mu hm N g hg)).
Qed.
