(** Federer (1969), 2.4.19, p. 91: fibre measures normalise the finite-image
    integral to a convex combination. These supporting identities use the
    disjoint additivity of 2.1.3 and the conull-domain convention of 2.3.2. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureStepFunctionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasurableFunctionUP MeasurableFunctionBorel TopologicalBorel
  MeasureFiniteAdditivity FatouNullRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_source_function_fibre]: supporting finite measurable
    fibres for the first case of Federer 2.4.19, p. 91 Finite total mass
    makes even the zero fibre finite. *)
Lemma finite_source_function_fibre (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) y :
  mu setT < +oo -> is_measure_measurable_function mu f ->
  measure_measurable mu (partial_function_preimage f [set y]) /\
  mu (partial_function_preimage f [set y]) \is a fin_num.
Proof.
move=> hfin hf; split.
- apply: (@measurable_function_borel_preimage R X [the topologicalType of real_norm_metric_space hN]
    mu hm f hf).
  apply: closed_borel_set; apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
- rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  apply: le_lt_trans _ hfin; apply: (@measure_mono R X mu hm); exact: subsetT.
Qed.

(** Source for [finite_fibre_mass_sum]: supporting total weight identity for
    the finite-image case of Federer 2.4.19, p. 91 Fibre masses sum to the
    total mass even for a conull partial domain. *)
Lemma finite_fibre_mass_sum (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (m : R) :
  mu setT=m%:E -> is_measure_measurable_function mu f -> finite_set (partial_function_range f) ->
  (\sum_(y <- fset_set (partial_function_range f)) fine (mu (partial_function_preimage f [set y])))%R=m.
Proof.
move=> hmX hf hfin; pose S := fset_set (partial_function_range f).
have hmu : mu setT < +oo by rewrite hmX ltry.
have hA y := @finite_source_function_fibre R X V N hN mu hm f y hmu hf.
have hdis y z : y \in S -> z \in S -> y != z ->
    forall x, partial_function_preimage f [set y] x -> partial_function_preimage f [set z] x -> False.
  move=> _ _ hyz x [a [ha hay]] [b [hb hbz]].
  have hab := partial_function_single_valued ha hb.
  apply: (negP hyz); apply/eqP; by rewrite -(hay : a=y) -(hbz : b=z).
have hsum := @measure_finite_disjoint_additivity R X V mu hm
  (fun y => partial_function_preimage f [set y]) S (fun y _ => (hA y).1) hdis.
have he : (\bigcup_(y in [set` S]) partial_function_preimage f [set y])=partial_function_domain f.
  apply/seteqP; split.
  - move=> x [y hy [z [hz _]]]; by exists z.
  - move=> x [y hy]; exists y; last by exists y; split.
    change (y \in S); rewrite /S in_fset_set //; apply/mem_set; by exists x.
have hdom := @measure_conull_intersection_value R X mu hm (partial_function_domain f) setT
  (measurable_function_domain hf).
rewrite setTI in hdom.
rewrite he hdom hmX in hsum.
apply: EFin_inj.
rewrite -sumEFin.
have hb : (\sum_(y <- S) (fine (mu (partial_function_preimage f [set y])))%:E)=
    \sum_(y <- S) mu (partial_function_preimage f [set y]).
  apply: eq_bigr=> y _; by rewrite fineK //; exact: (hA y).2.
by rewrite hb -hsum.
Qed.
