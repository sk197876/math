(** Federer (1969), 3.1.21, p. 234: an open
    parameter domain has the whole parameter space as its tangent. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  TangentConeUP TangentConeLocal TangentClosedSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_open_domain]: supporting parameter
    domains in the submanifold and constant-rank image assertions
    of Federer 3.1.21, p. 234. At an interior
    point of A, Tan(A,a) is the entire normed vector space,
    also when the vector space has dimension zero. *)
Lemma norm_tangent_open_domain (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (A:set X) a :
  norm_domain_interior N A a -> norm_tangent_cone N A a=setT.
Proof.
move=>hA.
pose Z:=@Subspace R X setT I (fun _ _ _ _=>I) (fun _ _ _=>I).
have hz:=@norm_tangent_closed_subspace R X N hN Z a (@closedT (real_norm_metric_space hN)) I.
change (norm_tangent_cone N setT a=setT) in hz.
have he:=@norm_tangent_open_restriction R X N setT A a hA.
rewrite setTI in he; exact (eq_trans he hz).
Qed.
