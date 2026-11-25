(** Supporting continuous reciprocal functions for the elementary integral
    evaluations in Federer (1969), 2.6.3(2), pp. 117–118 Clipping the input
    below the interval removes the irrelevant pole outside it and permits
    use of the project's globally continuous Riemann-integral interface. The
    original rational function is unchanged on the integration interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology normedtype lra.
From Federer Require Import UniformPrimitiveUP ReciprocalPrimitive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [clipped_reciprocal]: supporting continuous
    extension of the reciprocal outside the finite integration
    interval in Federer 2.6.3(2), pp. 117–118.
    The lower clipping threshold is kept explicit. *)
Definition clipped_reciprocal (R : realType) (a c x : R) : R :=
  (Order.max a x+c)^-1.

(** Source for [clipped_reciprocal_on]: supporting agreement
    with the actual rational formula on the interval of
    integration, Federer 2.6.3(2), pp. 117–118. *)
Lemma clipped_reciprocal_on (R : realType) (a c x : R) :
  a <= x -> clipped_reciprocal a c x=(x+c)^-1.
Proof. by move=> h; rewrite /clipped_reciprocal max_r. Qed.

(** Source for [clipped_reciprocal_continuous]: supporting
    continuity required by the Riemann sums in the elementary
    calculations of Federer 2.6.3(2), pp. 117–118. *)
Lemma clipped_reciprocal_continuous (R : realType) (a c : R) :
  0 < a+c -> continuous (clipped_reciprocal a c).
Proof.
move=> hac x; apply: (@continuousV R R^o (fun y => Order.max a y+c) x).
- have ham : a <= Order.max a x by rewrite le_max lexx.
  have hp : 0 < Order.max a x+c by lra.
  by rewrite (gt_eqF hp).
- apply: (@continuousD R R^o R^o (fun y => Order.max a y) (fun _ => c) x); last exact: cvg_cst.
  apply: continuous_max; [exact: cvg_cst | exact: cvg_id].
Qed.

(** Source for [clipped_reciprocal_uniform_primitive]: supporting reciprocal
    primitive rule on a finite interval with positive denominator in Federer
    2.6.3(2), pp. 117–118 *)
Lemma clipped_reciprocal_uniform_primitive (R : realType) (a b c : R) :
  0 < a+c -> is_uniform_primitive_on
    (fun x => -(clipped_reciprocal a c x)^+2) (clipped_reciprocal a c) a b.
Proof.
move=> hac; apply: (@affine_reciprocal_uniform_primitive R (clipped_reciprocal a c) a b c).
- exact: clipped_reciprocal_continuous.
- move=> x /andP[hax hxb]; split; first exact: clipped_reciprocal_on.
  have hp : 0 < x+c by lra.
  by rewrite (gt_eqF hp).
Qed.
