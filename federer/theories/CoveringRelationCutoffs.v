(** The cutoff relations in Federer (1969), 2.8.17, pp. 151–152. The support
    below isolates its order-theoretic part from the particular ratio. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import CoveringFamilyUP CoveringRelationUP CoveringRelationFineness
  CoveringRelationLimits PartialFunctionUP ExtendedRealBounds MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_value_cutoff]: the additional
    inequality in C_n in Federer 2.8.17, p. 151.
    This supporting restriction applies to any partial numerical
    function; restricting base points to Z is a separate step. *)
Definition covering_value_cutoff (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) (c : \bar R) :=
  fun x S => C x S /\ exists y, partial_function_graph f S y /\ y < c.

(** Source for [covering_value_cutoff_fine]: the assertion that C_n is fine
    on A_n in Federer 2.8.17, pp. 151–152 The larger relation supplies the
    upper bound, the fine subrelation supplies small sets, and definedness
    on the larger relation supplies actual function values. *)
Lemma covering_value_cutoff_fine (R : realType) (X : metricType R)
    (C V : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x c :
  (forall S, C x S -> V x S) ->
  (forall S, V x S -> partial_function_domain f S) ->
  covering_relation_fine_at C x -> covering_upper_limit V f x < c ->
  covering_relation_fine_at (covering_value_cutoff C f c) x.
Proof.
move=> hCV hdom hf /covering_upper_limit_lt_iff [d [hd hb]].
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
have hmin : (0 < Num.min e d)%R by rewrite lt_min he hd.
have [S [hC hdiam]] := (covering_relation_fine_iff_small_diameter C x).1 hf _ hmin.
have [y hy] := hdom S (hCV S hC).
have hsmall : extended_metric_diameter S < d%:E.
  apply: lt_le_trans hdiam _; rewrite lee_fin; by rewrite ge_min lexx orbT.
have hrange : covering_value_range V f x d y.
  exists S; split; first exact: hCV S hC.
  by split.
have hyc := le_lt_trans (extended_real_sup_upper hrange) hb.
exists S; split.
- split=> //; by exists y.
- apply: lt_le_trans hdiam _; rewrite lee_fin; by rewrite ge_min lexx.
Qed.

(** Source for [covering_context_subfamily]: the standing
    hypotheses for C_n(A_n) in the application of 2.8.7
    in Federer 2.8.17, p. 152. Closedness is inherited;
    measure, open measurability and bounded finiteness are unchanged. *)
Lemma covering_context_subfamily (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (F G : set (set X)) :
  is_covering_theory_context F phi -> G `<=` F -> is_covering_theory_context G phi.
Proof.
move=> hc hGF; constructor.
- exact: covering_context_measure hc.
- move=> S hS; exact (@covering_context_closed R X F phi hc S (hGF S hS)).
- exact: covering_context_open_measurable hc.
- exact: covering_context_bounded_finite hc.
Qed.
