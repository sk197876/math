(** Federer (1969), 2.2.7, pp. 63–64: consequences of the distance
    inequality and the least-constant specification. Source context and the
    positive/nonnegative convention are recorded in LipschitzUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_lipschitz_bound_increase]: supporting lemma
    for Federer 2.2.7, pp. 63–64: increasing a nonnegative bound
    preserves the distance inequality. *)
Lemma metric_lipschitz_bound_increase (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) M N :
  is_metric_lipschitz_bound X f M -> M <= N -> is_metric_lipschitz_bound X f N.
Proof.
move=> [hM hf] hMN; split; first exact: le_trans hM hMN.
move=> x y hx hy; apply: le_trans (hf x y hx hy) _.
apply: ler_wpM2r; [exact: mdist_ge0|exact hMN].
Qed.

(** Source for [metric_lipschitz_of_bound]: supporting equivalence for
    Federer 2.2.7, pp. 63–64. *)
Lemma metric_lipschitz_of_bound (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) M :
  is_metric_lipschitz_bound X f M -> is_metric_lipschitz X f.
Proof.
move=> hM; exists (M+1); split.
- have hge : 1 <= M+1 by rewrite lerDr; exact: hM.1.
  exact: lt_le_trans ltr01 hge.
- apply: metric_lipschitz_bound_increase hM _; by rewrite lerDl ler01.
Qed.

(** Source for [metric_lipschitz_bound_restrict]: supporting
    restriction law for Federer 2.2.7, p. 64, local definition:
    the same bound holds on every subset of its domain. *)
Lemma metric_lipschitz_bound_restrict (R : realType) (T U : metricType R)
    (X Y : set T) (f : T -> U) M :
  Y `<=` X -> is_metric_lipschitz_bound X f M -> is_metric_lipschitz_bound Y f M.
Proof. move=> hYX [hM hf]; split=> // x y hx hy; exact: hf x y (hYX x hx) (hYX y hy). Qed.

(** Source for [least_metric_lipschitz_unique]: supporting uniqueness
    of Lip(f) in Federer 2.2.7, p. 64: two least attained bounds
    are equal, using only the abstract specification. *)
Lemma least_metric_lipschitz_unique (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) L M :
  is_least_metric_lipschitz_constant X f L ->
  is_least_metric_lipschitz_constant X f M -> L = M.
Proof.
move=> hL hM; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (least_metric_lipschitz_minimal hL (least_metric_lipschitz_bound hM)).
- exact: (least_metric_lipschitz_minimal hM (least_metric_lipschitz_bound hL)).
Qed.

(** Source for [metric_lipschitz_constant_map]: supporting zero-bound
    boundary case for Federer 2.2.7, p. 64; a constant map has least
    nonnegative bound zero, in accordance. *)
Lemma metric_lipschitz_constant_map (R : realType) (T U : metricType R)
    (X : set T) (a : U) : is_least_metric_lipschitz_constant X (fun _ => a) 0.
Proof.
constructor.
- split; first exact: lexx.
  by move=> x y _ _; rewrite mdistxx mul0r.
- by move=> M [hM _].
Qed.

(** Source for [metric_lipschitz_empty]: supporting empty-domain
    case for Federer 2.2.7, p. 64: the distance inequality is
    vacuous, and the least nonnegative bound is zero. *)
Lemma metric_lipschitz_empty (R : realType) (T U : metricType R) (f : T -> U) :
  is_least_metric_lipschitz_constant set0 f 0.
Proof. constructor; [split=> // x y []|by move=> M [hM _]]. Qed.

(** Source for [metric_lipschitz_is_local]: supporting relation
    between the two definitions in Federer 2.2.7, p. 64: a
    global bound supplies the required bound in the whole-space
    neighborhood of every point. *)
Lemma metric_lipschitz_is_local (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) :
  is_metric_lipschitz X f -> is_locally_metric_lipschitz X f.
Proof.
move=> [M [hM hf]] x hx; exists setT; split; first exact: filterT.
exists M; split=> //; rewrite setIT; exact hf.
Qed.
