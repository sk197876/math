(** Federer (1969), 2.2.7, p. 64, the displayed upper limit of local
    distance quotients. We use the equivalent eventual-bound formulation:
    every L greater than M bounds the quotient in a sufficiently small
    punctured ball. The center itself satisfies the undivided inequality
    automatically. No differentiability is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_metric_local_slope_bound]: Federer 2.2.7,
    p. 64, paraphrase of the displayed limsup inequality, in its
    eventual-bound form. For every L greater than M, nearby pairs
    with fixed center have image distance at most L times domain
    distance. Inserting the center makes no difference because
    both distances there are zero. *)
Definition is_metric_local_slope_bound (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (M : R) : Prop :=
  forall x, X x -> forall L, M < L -> exists d,
    0 < d /\ forall y, X y -> mdist x y < d ->
      mdist (f x) (f y) <= L * mdist x y.

(** Source for [metric_bound_is_local_slope_bound]: Federer 2.2.7, p. 64,
    necessity in the convex-domain equivalence. This direction needs no
    convexity: a global distance bound bounds every local quotient. *)
Lemma metric_bound_is_local_slope_bound (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) M :
  is_metric_lipschitz_bound X f M -> is_metric_local_slope_bound X f M.
Proof.
move=> [hM hf] x hx L hL; exists 1; split; first exact: ltr01.
move=> y hy _; apply: le_trans (hf x y hx hy) _.
apply: ler_wpM2r; [exact: mdist_ge0|exact: ltW hL].
Qed.
