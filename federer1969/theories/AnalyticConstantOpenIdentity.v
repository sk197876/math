(** Federer (1969), 3.4.8(11), p. 333:
    a nonconstant analytic function cannot be
    constant on a nonempty open neighbourhood
    in a connected domain. This is a
    direct connection to the project's analytic
    identity theorem from 3.1.24. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormAnalyticUP NormAnalyticLocal NormAnalyticConstant
  NormAnalyticOperations NormRegularity AnalyticIdentityOpenZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_constant_open_identity]:
    the nonconstant-neighbourhood assertion for Psi
    in 3.4.8(11), p. 333, follows
    by applying the existing identity theorem
    to f minus its local constant. *)
Theorem analytic_constant_open_identity (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A U:set X) (f:X->R^o) a c:
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f ->
  @open (real_norm_metric_space hNX) U ->U a ->U `<=` A ->
  (forall x,U x ->f x = c) ->forall x,A x ->f x = c.
Proof.
move=>hConnected hAnalytic hU hUa hUA hConstant.
have hClassZero:=norm_class_continuous (norm_analytic_class_all_orders hAnalytic 0%N).
have hOpen x (hx:A x):norm_domain_interior NX A x.
  exact:(@hClassZero x hx).1.
have hC:=@norm_constant_analytic R X R^o NX (fun z:R^o=>`|z|) hNX
  (@scalar_absolute_value_norm R) A hOpen c.
have hDifference:=norm_analytic_subtract hAnalytic hC.
have hZero:forall x,U x ->f x-c = 0 by move=>x hx;rewrite hConstant // subrr.
have hIdentity:=@analytic_identity_open_zero R X R^o NX (fun z:R^o=>`|z|) hNX
  (@scalar_absolute_value_norm R) A U (fun x=>f x-c) a hConnected hDifference hU hUa hUA hZero.
move=>x hx;apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hIdentity x hx.
Qed.
