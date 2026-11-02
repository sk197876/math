(** Federer (1969), 3.1.1, p. 210: quantitative local invertibility
    of a map whose difference from the identity is a strict contraction
    on a closed ball. Completeness is used only for existence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP InverseFunctionIterationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [near_identity_norm_lower_bound]: the lower increment
    bound for f in Federer 3.1.1, p. 210, derived from the contraction
    estimate for g=f-identity. It holds on any prescribed subset. *)
Lemma near_identity_norm_lower_bound (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) (f : X -> X)
    (A : X -> Prop) (c : R) :
  (forall x z, A x -> A z -> N ((f x-x)-(f z-z)) <= c*N (x-z)) ->
  forall x z, A x -> A z -> (1-c)*N (x-z) <= N (f x-f z).
Proof.
move=> hf x z hx hz.
have heq : (f x-f z)-(x-z) = (f x-x)-(f z-z).
  by rewrite !opprB !addrA [f x-f z+z]addrAC
    [f x+z-f z-x]addrAC [f x-x+z]addrAC.
have htri : N (x-z) <= N (f x-f z)+N ((f x-x)-(f z-z)).
  rewrite -heq -{1}(subKr (f x-f z) (x-z)).
  apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
  by rewrite (real_seminorm_negate hN.1).
have hb := hf x z hx hz; by nra.
Qed.

(** Source for [near_identity_norm_injective]: the positive lower
    bound in Federer 3.1.1, p. 210, makes f one-to-one on the ball. *)
Lemma near_identity_norm_injective (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) (f : X -> X)
    (A : X -> Prop) (c : R) :
  c < 1 ->
  (forall x z, A x -> A z -> N ((f x-x)-(f z-z)) <= c*N (x-z)) ->
  forall x z, A x -> A z -> f x = f z -> x = z.
Proof.
move=> hc hf x z hx hz he.
have hb := near_identity_norm_lower_bound hN hf hx hz; rewrite he subrr (real_seminorm_zero hN.1) in hb.
have hn := real_seminorm_nonnegative hN.1 (x-z).
have hzero : N (x-z) = 0 by nra.
exact: subr0_eq (hN.2 _ hzero).
Qed.

(** Source for [near_identity_norm_ball_surjective]: the smaller
    closed ball is contained in the image in Federer 3.1.1, p. 210.
    The printed B notation denotes closed balls (2.8.1, p. 141).
    The fixed-point witness is proved by the corrected iteration. *)
Theorem near_identity_norm_ball_surjective (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (f : X -> X) (c r : R) :
  f 0 = 0 -> 0 < c < 1 -> 0 < r ->
  (forall x z, N x <= r -> N z <= r -> N ((f x-x)-(f z-z)) <= c*N (x-z)) ->
  forall y, N y <= (1-c)*r -> exists x, N x <= r /\ f x = y.
Proof.
move=> hf0 hc hr hf y hy.
have hg0 : (fun x => f x-x) 0 = 0 by rewrite hf0 subrr.
have [x [hx he]] := @inverse_function_iteration_solution R X N hN hcomplete
  (fun x => f x-x) y c r hg0 hc hr hy hf.
exists x; split=> //.
have hh := congr1 (fun z => z+(f x-x)) he.
by rewrite subrKC subrK in hh.
Qed.
