(** Federer (1969), 3.4.8(11), p. 333:
    the analytic barrier is not constant on
    any neighbourhood in its connected domain.
    This supporting connection applies the existing
    analytic identity theorem to two distinct values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormAnalyticUP AnalyticConstantOpenIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_nonconstant_nowhere_locally_constant]:
    the nonconstant-neighbourhood step for Psi
    in 3.4.8(11), p. 333. The
    actual two different values, rather than
    an assumed critical-set dimension, suffice. *)
Theorem analytic_nonconstant_nowhere_locally_constant (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (f:X->R^o) b c:
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f ->
  A b ->A c ->f b<>f c ->forall a,
  ~(exists r:R,0<r /\ forall x,NX (x-a)<r ->A x /\ f x = f a).
Proof.
move=>hConnected hAnalytic hAb hAc hDifferent a [r [hr hConstant]].
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose U:set X:=[set x|NX (x-a)<r].
have hUa:U a.
  change (NX (a-a)<r);by rewrite subrr (real_seminorm_zero hNX.1).
have hUOpen:@open T U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1
    (@norm_open_ball_domain_interior R X NX hNX a r x hx).
have hUA:U `<=` A by move=>x hx;exact:(hConstant x hx).1.
have hValue:forall x,U x ->f x = f a by move=>x hx;exact:(hConstant x hx).2.
have hIdentity:=@analytic_constant_open_identity R X NX hNX A U f a (f a)
  hConnected hAnalytic hUOpen hUa hUA hValue.
apply:hDifferent;by rewrite (hIdentity b hAb) (hIdentity c hAc).
Qed.
