(** Federer (1969), 2.4.19, p. 91: g takes values in C almost everywhere.
    These supporting null replacements reduce the partial-domain convention
    of 2.3.2, p. 73, to a total map taking every value in C. No topology of
    C is required for this null modification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialFunctionExtensionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableNormedBasic
  MeasureLpMembershipUP MeasureLpAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_measure_conull_range_nonempty]: supporting
    nonemptiness of C in Federer 2.4.19, p. 91,
    forced by positive total measure and the conull range hypothesis. *)
Lemma positive_measure_conull_range_nonempty (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (f : partial_function X Y) (C : set Y) :
  mu setT != 0 -> measure_almost_everywhere mu (partial_function_preimage f C) -> C !=set0.
Proof.
move=> hm hC; apply: contrapT=> hn.
have he : partial_function_preimage f C=set0.
  apply/seteqP; split; last by move=> x [].
  move=> x [y [_ hy]]; apply: hn; by exists y.
move: hC; rewrite /measure_almost_everywhere he setC0=> hz.
by move: hm; rewrite hz eqxx.
Qed.

(** Source for [measure_lp_total_range_representative]: supporting total
    C-valued reduction for Federer 2.4.19, p. 91 Lp membership and all
    integral values are unchanged by the null modification. *)
Lemma measure_lp_total_range_representative (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) (C : set V) :
  mu setT != 0 -> is_measure_lp_function mu p f ->
  measure_almost_everywhere mu (partial_function_preimage f C) ->
  exists G : X -> real_norm_metric_space hN,
    (forall x, C (G x)) /\ is_measure_lp_function mu p (partial_function_total G) /\
    measure_almost_equal mu f (partial_function_total G).
Proof.
move=> hmass hf hC.
have [c hc] := @positive_measure_conull_range_nonempty R X V mu f C hmass hC.
have [g [hg [ha hmg]]] := @measurable_normed_total_representative R X V N hN mu hm f hf.2.1.
pose G x := (if pselect (C (g x)) then g x else c : real_norm_metric_space hN).
have hGC x : C (G x) by rewrite /G; case: pselect=> hx.
have he : measure_almost_equal mu f (partial_function_total G).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hC)=> x [y [hy hCy]].
  exists y; split=> //; change (G x=y).
  rewrite /G (hg x y hy); case: pselect=> hx //.
exists G; split=> //; split=> //.
exact: (@measure_lp_function_almost_equal R X V N hN mu hm p f _ hf he).
Qed.

(** Source for [measure_almost_equal_postcompose]: supporting invariance of
    F composed with g under the null replacement in Federer 2.4.19, p. 91
    This graph fact requires no continuity of F. *)
Lemma measure_almost_equal_postcompose (R : realType) (X : choiceType) (Y Z : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X Y) (F : Y -> Z) :
  measure_almost_equal mu f g ->
  measure_almost_equal mu (partial_function_postcompose f F) (partial_function_postcompose g F).
Proof.
move=> he; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x [y [hf hg]].
exists (F y); split; exists y; by split.
Qed.
