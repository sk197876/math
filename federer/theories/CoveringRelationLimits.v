(** Federer (1969), 2.8.16, p. 151, final paragraph: upper, lower and
    ordinary limits along a covering relation. The monotone epsilon limits
    are expressed through the existing sealed extended infimum and supremum,
    not an external differentiation or filter library. Value expressions are
    total; the book uses them at points where the relation is fine. The
    ordinary limit has an explicit partial-function graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import CoveringRelationUP CoveringRelationFineness
  MetricDiameter ExtendedRealBounds PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_value_range]: the set inside the epsilon-dependent
    supremum of Federer 2.8.16, p. 151. Requiring a graph value enforces S
    in dmn f; no value outside the domain is assigned. *)
Definition covering_value_range (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) (x : X) (e : R) :=
  [set y | exists S, C x S /\ extended_metric_diameter S < e%:E /\ partial_function_graph f S y].

(** Source for [covering_upper_limit]: the upper-limit formula in Federer
    2.8.16, p. 151 The supremum increases with epsilon, so its limit as
    epsilon decreases to zero is its infimum over positive epsilon. Empty
    ranges have supremum -infinity. *)
Definition covering_upper_limit (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) (x : X) :=
  extended_real_inf [set b | exists e : R, (0 < e)%R /\ b = extended_real_sup (covering_value_range C f x e)].

(** Source for [covering_lower_limit]: the analogous lower limit requested
    in Federer 2.8.16, p. 151 It is the supremum of the small-radius infima;
    an empty infimum is +infinity. *)
Definition covering_lower_limit (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) (x : X) :=
  extended_real_sup [set b | exists e : R, (0 < e)%R /\ b = extended_real_inf (covering_value_range C f x e)].

(** Source for [covering_relation_limit]: the ordinary limit of Federer
    2.8.16, p. 151 The book introduces this notation at fine points. The
    graph therefore also requires fineness there. *)
Definition covering_relation_limit (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) : partial_function X (\bar R).
Proof.
refine (@Build_partial_function X (\bar R) (fun x y =>
  covering_relation_fine_at C x /\ covering_upper_limit C f x = y /\ covering_lower_limit C f x = y) _).
by move=> x y z [_ [<- _]] [_ [<- _]].
Defined.

(** Source for [covering_value_range_mono]: supporting epsilon monotonicity
    of the upper/lower-limit formula in Federer 2.8.16, p. 151 *)
Lemma covering_value_range_mono (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x e d :
  (e <= d)%R -> covering_value_range C f x e `<=` covering_value_range C f x d.
Proof.
move=> hed y [S [hS [hdiam hf]]]; exists S; split=> //; split=> //.
apply: lt_le_trans hdiam _; by rewrite lee_fin.
Qed.

(** Source for [covering_upper_limit_le_level]: supporting infimum bound for
    the monotone epsilon limit in Federer 2.8.16, p. 151 *)
Lemma covering_upper_limit_le_level (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x e :
  (0 < e)%R -> covering_upper_limit C f x <= extended_real_sup (covering_value_range C f x e).
Proof. move=> he; apply: extended_real_inf_lower; by exists e. Qed.

(** Source for [covering_lower_limit_ge_level]: the dual
    supporting bound for Federer 2.8.16, p. 151. *)
Lemma covering_lower_limit_ge_level (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x e :
  (0 < e)%R -> extended_real_inf (covering_value_range C f x e) <= covering_lower_limit C f x.
Proof. move=> he; apply: extended_real_sup_upper; by exists e. Qed.

(** Source for [covering_upper_limit_lt_iff]: supporting
    eventual strict upper bound for the expression in Federer
    2.8.16, p. 151, used in the proof of 2.8.17,
    pp. 151–152. This is an infimum order consequence,
    without assuming that f is defined on every related set. *)
Lemma covering_upper_limit_lt_iff (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x c :
  covering_upper_limit C f x < c <->
    exists e : R, (0 < e)%R /\ extended_real_sup (covering_value_range C f x e) < c.
Proof.
split.
- move=> hl; apply: contrapT=> hn.
  have hge : c <= covering_upper_limit C f x.
    apply: extended_real_inf_greatest=> b [e [he ->]].
    rewrite leNgt; apply/negP=> hb; apply: hn; by exists e.
  by have := le_lt_trans hge hl; rewrite ltxx.
- move=> [e [he hb]]; exact: le_lt_trans (covering_upper_limit_le_level C f x he) hb.
Qed.

(** Source for [covering_limits_ordered]: the domain-sensitive order
    assertion supporting Federer 2.8.16, p. 151 The restricted relation on
    dmn f must be fine; fineness of C alone is insufficient. *)
Lemma covering_limits_ordered (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x :
  covering_relation_fine_at (fun x S => C x S /\ partial_function_domain f S) x ->
  covering_lower_limit C f x <= covering_upper_limit C f x.
Proof.
move=> hf; apply: extended_real_sup_least=> b [e [he ->]].
apply: extended_real_inf_greatest=> c [d [hd ->]].
have hmin : (0 < Num.min e d)%R by rewrite lt_min he hd.
have [S [[hS [y hy]] hdiam]] :=
  (covering_relation_fine_iff_small_diameter _ x).1 hf _ hmin.
have hSe : covering_value_range C f x e y.
  exists S; split=> //; split=> //.
  apply: lt_le_trans hdiam _; rewrite lee_fin; by rewrite ge_min lexx.
have hSd : covering_value_range C f x d y.
  exists S; split=> //; split=> //.
  apply: lt_le_trans hdiam _; rewrite lee_fin; by rewrite ge_min lexx orbT.
exact: le_trans (extended_real_inf_lower hSe) (extended_real_sup_upper hSd).
Qed.

(** Source for [covering_limit_domain]: the ordinary-limit existence
    convention in Federer 2.8.16, p. 151 Values at nonfine points are
    excluded, and agreement determines the limit uniquely. *)
Lemma covering_limit_domain (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x :
  partial_function_domain (covering_relation_limit C f) x <->
  covering_relation_fine_at C x /\ covering_upper_limit C f x = covering_lower_limit C f x.
Proof.
split.
- by move=> [y [hf [hu hl]]]; split=> //; rewrite hu hl.
- move=> [hf h]; exists (covering_upper_limit C f x); split=> //; by split=> //; rewrite h.
Qed.


(** Source for [covering_upper_limit_empty_function]: the domain
    qualification in Federer 2.8.16, p. 151 If f is nowhere defined, every
    upper-range supremum is -infinity. *)
Lemma covering_upper_limit_empty_function (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) x :
  covering_upper_limit C (@partial_function_empty (set X) (\bar R)) x = -oo.
Proof.
apply/eqP; rewrite eq_le leNye andbT.
have hb := covering_upper_limit_le_level C (@partial_function_empty (set X) (\bar R)) x (@ltr01 R).
have he : covering_value_range C (@partial_function_empty (set X) (\bar R)) x 1 = set0.
  by apply/seteqP; split=> [y [S [_ [_ []]]]|y []].
by rewrite he extended_real_sup_empty in hb.
Qed.

(** Source for [covering_lower_limit_empty_function]: the dual empty-domain
    convention for Federer 2.8.16, p. 151 *)
Lemma covering_lower_limit_empty_function (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) x :
  covering_lower_limit C (@partial_function_empty (set X) (\bar R)) x = +oo.
Proof.
apply/eqP; rewrite eq_le leey /=.
have hb := covering_lower_limit_ge_level C (@partial_function_empty (set X) (\bar R)) x (@ltr01 R).
have he : covering_value_range C (@partial_function_empty (set X) (\bar R)) x 1 = set0.
  by apply/seteqP; split=> [y [S [_ [_ []]]]|y []].
by rewrite he extended_real_inf_empty in hb.
Qed.
