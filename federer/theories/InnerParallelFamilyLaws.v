(** Federer (1969), 4.1.4, pp. 348–349: the original
    inward loci lie in A, grow as the radius decreases and
    carry the radius-e closed balls needed for kernel support.
    Openness of A supplies every point at all small radii. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  InnerParallelFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section InnerParallelFamilyLaws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable A:set X.
Variable O:R->set X.
Hypothesis hO:is_inner_parallel_family NX A O.

(** Source for [inner_parallel_inside]: the original inward locus
    is contained in A, Federer 4.1.4, p. 348. *)
Lemma inner_parallel_inside e:0<e ->O e `<=` A.
Proof. move=>he x hx; exact:((@hO e he x).1 hx).1. Qed.

(** Source for [inner_parallel_reverse_monotone]: decreasing
    epsilon enlarges the original inward locus, supporting
    the components C_e in Federer 4.1.4, pp. 348–349. *)
Lemma inner_parallel_reverse_monotone e d:
  0<e ->0<d ->e<=d ->O d `<=` O e.
Proof.
move=>he hd hed x hx.
have[hxA [r [hdr hBall]]]:=(@hO d hd x).1 hx.
apply:(@hO e he x).2; split=>//; exists r; split; first exact:le_lt_trans hed hdr.
exact hBall.
Qed.

(** Source for [inner_parallel_closed_ball_inside]: the closed
    epsilon ball about an inward point lies in A, the actual
    support inclusion used for smoothing in Federer 4.1.4,
    pp. 348–349. *)
Lemma inner_parallel_closed_ball_inside e:0<e ->forall x,
  O e x ->forall y,NX (y-x)<=e ->A y.
Proof.
move=>he x hx y hy.
have[_ [r [her hBall]]]:=(@hO e he x).1 hx.
apply:hBall; exact:le_lt_trans hy her.
Qed.

(** Source for [inner_parallel_eventually_contains]: every
    original point belongs to all sufficiently small inward
    loci, supporting the component exhaustion in Federer
    4.1.4, pp. 348–349. *)
Lemma inner_parallel_eventually_contains:
  @open (real_norm_metric_space hNX) A ->forall x,A x ->
  exists d:R,0<d /\ forall e:R,0<e ->e<d ->O e x.
Proof.
move=>hA x hx.
have hNbhs:nbhs (x:real_norm_metric_space hNX) A by move:hA; rewrite openE; exact.
have[d [hd hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX A x).2 hNbhs.
exists d; split=>// e he hed; apply:(@hO e he x).2.
split=>//; exists d; split=>// y hy.
have h:=hBall (y-x) hy; by rewrite addrC subrK in h.
Qed.
End InnerParallelFamilyLaws.
