(** Federer (1969), 4.1.24, p. 382:
    the integral flat quantity metrises an
    additive group. No closure under real
    multiplication, or real homogeneity, is
    part of this metric construction. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_additive_size]: the zero,
    symmetry, separation and triangle laws
    behind the metric in Federer 4.1.24,
    p. 382. These are independent laws
    on an additive group, not real norm axioms. *)
Record is_additive_size (R:realType) (G:zmodType)
    (N:G->R):Prop:={
  (** Source: zero has zero integral flat cost,
      Federer 4.1.24, p. 382. *)
  additive_size_zero:N 0=0;
  (** Source: every mass-decomposition cost is
      nonnegative, Federer 4.1.24, p. 382. *)
  additive_size_nonnegative:forall x,0<=N x;
  (** Source: negating both decomposition terms
      preserves cost, Federer 4.1.24, p. 382. *)
  additive_size_opposite:forall x,N (-x)=N x;
  (** Source: the displayed subadditivity in
      Federer 4.1.24, p. 382. *)
  additive_size_triangle:forall x y,N (x+y)<=N x+N y;
  (** Source: the metric separates actual currents,
      Federer 4.1.24, p. 382, by F_K
      bounded above by the integral flat quantity. *)
  additive_size_definite:forall x,N x=0->x=0
}.

(** Source for [additive_size_metric_space]:
    the additive group equipped with the
    original distance, Federer 4.1.24,
    p. 382. The carrier is supplied
    independently; no scalar multiplication is added. *)
Definition additive_size_metric_space (R:realType) (G:zmodType)
    (N:G->R) (_:is_additive_size N):Type:=G.
HB.instance Definition _ (R:realType) (G:zmodType)
    (N:G->R) (hN:is_additive_size N):=
  GRing.Zmodule.copy (additive_size_metric_space hN) G.

Section Metric.
Variable R:realType.
Variable G:zmodType.
Variable N:G->R.
Hypothesis hN:is_additive_size N.
Local Notation M := (additive_size_metric_space hN).

(** Source for [additive_size_distance]:
    the printed distance is the integral
    flat quantity of T_1-T_2, Federer
    4.1.24, p. 382. *)
Definition additive_size_distance (x y:M):R:=N (x-y).

(** Source for [additive_size_distance_self]:
    equality has distance zero in the
    metric of Federer 4.1.24, p. 382. *)
Lemma additive_size_distance_self x:
  additive_size_distance x x=0.
Proof.
by rewrite /additive_size_distance subrr (additive_size_zero hN).
Qed.

(** Source for [additive_size_distance_separates]:
    distance zero identifies actual integral
    flat chains, Federer 4.1.24, p. 382. *)
Lemma additive_size_distance_separates x y:
  additive_size_distance x y=0->x=y.
Proof.
move=>h.
have hDifference:N ((x:G)-(y:G))=0:=h.
have hZero:(x:G)-(y:G)=0:=@additive_size_definite R G N hN ((x:G)-(y:G)) hDifference.
change ((x:G)=(y:G)).
apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hZero.
Qed.

(** Source for [additive_size_distance_symmetric]:
    negating a difference preserves integral
    flat cost, Federer 4.1.24, p. 382. *)
Lemma additive_size_distance_symmetric x y:
  additive_size_distance x y=additive_size_distance y x.
Proof.
have h:x-y= -(y-x) by rewrite opprB.
by rewrite /additive_size_distance h (additive_size_opposite hN).
Qed.

(** Source for [additive_size_distance_triangle]:
    the printed subadditivity gives the
    distance triangle inequality, Federer
    4.1.24, p. 382. *)
Lemma additive_size_distance_triangle y x z:
  additive_size_distance x z<=
    additive_size_distance x y+additive_size_distance y z.
Proof.
rewrite /additive_size_distance.
have h:x-z=(x-y)+(y-z) by rewrite addrA subrK.
rewrite h.
exact:(@additive_size_triangle R G N hN ((x:G)-(y:G)) ((y:G)-(z:G))).
Qed.

HB.instance Definition _ := isMetric.Build R M
  additive_size_distance_self additive_size_distance_separates
  additive_size_distance_symmetric additive_size_distance_triangle.

(** Source for [additive_size_metric_distanceE]:
    the topology uses exactly the original
    integral flat distance, Federer 4.1.24,
    p. 382. *)
Lemma additive_size_metric_distanceE (x y:M):
  mdist x y=N (x-y).
Proof. by []. Qed.
End Metric.
