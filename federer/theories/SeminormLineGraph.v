(** Federer (1969), 1.10.5, p. 48: supporting norming functional, following
    the one-vector corollary in 2.4.12, p. 86. The line construction
    includes a zero vector and vectors in the kernel of a seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RealNormUP PartialLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Line.
Variable R : realFieldType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variable v : V.

(** Source for [seminorm_line_graph]: Federer 1.10.5,
    p. 48, the supporting line functional from 2.4.12, p. 86:
    assign t*N(v) to t*v. *)
Definition seminorm_line_graph (x : V) (a : R^o) :=
  exists t : R, x=t *: v /\ a=t*N v.

(** Source for [seminorm_line_graph_linear]: Federer 1.10.5,
    p. 48, the proposed line values form a linear graph,
    including when v=0. *)
Lemma seminorm_line_graph_linear : linear_graph seminorm_line_graph.
Proof.
split.
- exists 0; by rewrite scale0r mul0r.
split.
- move=> x y a b [s [-> ->]] [t [-> ->]]; exists (s+t).
  by rewrite scalerDl mulrDl.
split.
- move=> c x a [t [-> ->]]; exists (c*t).
  split; first by rewrite scalerA.
  change (c*(t*N v) = (c*t)*N v); exact: mulrA.
- move=> x a b [s [hs ->]] [t [ht ->]].
  case: (eqVneq v 0)=> [hv|hv].
  + by rewrite hv (real_seminorm_zero hN) !mulr0.
  + have hz : (s-t) *: v=0 by rewrite scalerBl -hs -ht subrr.
    have hst : s=t.
      move/eqP: hz; by rewrite scaler_eq0 (negPf hv) orbF subr_eq0=> /eqP.
    by rewrite hst.
Qed.

(** Source for [seminorm_line_graph_dominated]: Federer
    1.10.5, p. 48, the line functional is dominated by the
    seminorm, since t*N(v) <= |t|*N(v)=N(t*v). *)
Lemma seminorm_line_graph_dominated x a : seminorm_line_graph x a -> a<=N x.
Proof.
move=> [t [-> ->]]; rewrite (real_seminorm_scale hN).
change (is_true (t*N v <= `|t|*N v)).
apply: ler_wpM2r; first exact: real_seminorm_nonnegative hN v.
exact: ler_norm.
Qed.

(** Source for [seminorm_line_graph_norms_vector]: Federer
    1.10.5, p. 48, the line functional attains the seminorm at v. *)
Lemma seminorm_line_graph_norms_vector : seminorm_line_graph v (N v).
Proof. exists 1; by rewrite scale1r mul1r. Qed.
End Line.
