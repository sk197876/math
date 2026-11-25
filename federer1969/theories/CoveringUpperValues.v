(** Strict upper-limit approximation supporting Federer (1969), 2.9.4, p.
    154, final proof display. The covering limits are those of 2.8.16, p.
    151; graph values enforce the original partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import CoveringRelationLimits MetricDiameter PartialFunctionUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_upper_limit_large_value]: supporting
    approximation of the strict upper-limit premise of
    Federer 2.9.4, p. 154. Every positive
    scale has a defined value above any smaller threshold;
    no value is supplied outside the function's domain. *)
Lemma covering_upper_limit_large_value (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R))
    x (b : \bar R) (e : R) :
  b<covering_upper_limit V f x -> (0<e)%R ->
  exists S y, V x S /\ extended_metric_diameter S<e%:E /\
    partial_function_graph f S y /\ b<y.
Proof.
move=> hl he.
have hsup : b<extended_real_sup (covering_value_range V f x e) :=
  lt_le_trans hl (@covering_upper_limit_le_level R X V f x e he).
apply: contrapT=> hn.
have hb : extended_real_sup (covering_value_range V f x e)<=b.
  apply: extended_real_sup_least=> y [S [hS [hd hf]]].
  rewrite leNgt; apply/negP=> hy; apply: hn; exists S,y; by split=> //; split=> //; split.
by have := lt_le_trans hsup hb; rewrite ltxx.
Qed.

(** Source for [covering_lower_limit_bound_by_small_values]:
    supporting lower-limit estimate in the reciprocal step
    of Federer 2.9.4, p. 154. Arbitrarily
    small defined values bounded by b bound the lower
    covering limit, without asserting an ordinary limit. *)
Lemma covering_lower_limit_bound_by_small_values (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x b :
  (forall e : R, (0<e)%R -> exists S y, V x S /\
    extended_metric_diameter S<e%:E /\ partial_function_graph f S y /\ y<=b) ->
  covering_lower_limit V f x<=b.
Proof.
move=> h; apply: extended_real_sup_least=> z [e [he ->]].
have [S [y [hS [hd [hf hy]]]]] := h e he.
apply: le_trans _ hy; apply: extended_real_inf_lower; by exists S.
Qed.
