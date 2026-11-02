(** Federer (1969), 1.7.1, p. 28: bounded compactness for the metric |x-y|.
    Boundedness is specified by a norm bound and proved equivalent to a
    metric ball bound with arbitrary centre. Source context are recorded in
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets topology num_normedtype
  pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  InnerMetric InnerNormedTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Boundedness.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Local Notation N := (inner_norm hB).

(** Source for [inner_bounded]: Federer 1.7.1, p. 28,
    boundedness in the specified metric, expressed by a bound on |x|. *)
Definition inner_bounded (A : set M) := exists r : R, forall x, A x -> N x <= r.

(** Source for [inner_bounded_metric]: Federer 1.7.1,
    p. 28, the norm-bound definition is equivalent to containment
    in a metric ball with some centre and finite radius. *)
Theorem inner_bounded_metric A : inner_bounded A <->
  exists a : M, exists r : R, forall x, A x -> @inner_distance R V B hB a x <= r.
Proof.
split.
- move=> [r hr]; exists 0, r => x hx.
  by rewrite /inner_distance sub0r inner_normN; exact: hr.
- move=> [a [r hr]]; exists (N a+r) => x hx.
  have h := @inner_norm_triangle R V B hB (x-a) a.
  rewrite subrK in h; apply: (le_trans h).
  rewrite [N a+r]addrC lerD2r.
  change (@inner_distance R V B hB x a <= r).
  rewrite inner_distance_sym; exact: hr.
Qed.

(** Source for [inner_boundedly_compact]: Federer 1.7.1,
    p. 28, bounded compactness: every closed bounded set is compact.
    The topology and boundedness use the already verified metric. *)
Definition inner_boundedly_compact :=
  forall A : set M, closed A -> inner_bounded A -> compact A.

(** Source for [inner_norm_sublevel_closed]: Federer
    1.7.1, p. 28, supporting closedness of a norm-bounded ball.
    General norm-topology continuity applies to the proved norm laws. *)
Lemma inner_norm_sublevel_closed r : closed [set x : M | N x <= r].
Proof.
have he : [set x : M | N x <= r] = closed_ball_ (fun x : M => N x) 0 r.
  by apply: funext => x; rewrite /closed_ball_ /= sub0r inner_normN.
rewrite he; exact: closed_closed_ball_.
Qed.

(** Source for [inner_unit_ball]: Federer 1.7.1, p. 28,
    the closed unit ball used in the reverse compactness implication. *)
Definition inner_unit_ball : set M := [set x | N x <= 1].

(** Source for [inner_unit_ball_closed]: Federer 1.7.1,
    p. 28, the unit ball is closed in the induced topology. *)
Lemma inner_unit_ball_closed : closed inner_unit_ball.
Proof. exact: inner_norm_sublevel_closed. Qed.

(** Source for [inner_unit_ball_bounded]: Federer 1.7.1,
    p. 28, the unit ball has the bound one. *)
Lemma inner_unit_ball_bounded : inner_bounded inner_unit_ball.
Proof. exists 1 => x; by []. Qed.

(** Source for [inner_unit_ball_compact]: Federer 1.7.1,
    p. 28, bounded compactness makes the closed unit ball compact. *)
Lemma inner_unit_ball_compact : inner_boundedly_compact -> compact inner_unit_ball.
Proof. move=> h; exact: h inner_unit_ball_closed inner_unit_ball_bounded. Qed.
End Boundedness.
