(** Federer (1969), 3.4.8(10), p. 331:
    extend an original germ identity across
    a common connected analytic domain. This
    applies the identity theorem already proved
    for 3.1.24, p. 240, and used
    in 3.4.5, p. 319. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP NormAnalyticOperations
  LocalGermUP LocalGermSealed AnalyticGermRepresentatives AnalyticGermUP AnalyticIdentityOpenZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_connected_agreement]:
    the identity involving W'_(m+1), t_(m+1),
    delta and s_(m+1) holds throughout the
    common prefix cylinder, 3.4.8(10), p. 331.
    A small convex prefix neighbourhood makes
    that cylinder connected. This connection
    retains arbitrary connected open domains. *)
Theorem analytic_germ_connected_agreement (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (A:set X)
    (f g:@analytic_representative_type R X NX hNX a):
  @open (real_norm_metric_space hNX) A ->A a ->
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value f) ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value g) ->
  analytic_germ f=analytic_germ g ->
  forall x,A x ->analytic_representative_value f x=analytic_representative_value g x.
Proof.
move=>hOpen ha hConnected hf hg hGerm.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
have hLocal:=(@local_germ_equality T R P value a _ _
  (@LocalGerms.laws T R P value a) f g).1 hGerm.
have [U [hU [haU hValues]]]:=hLocal.
pose V:=U `&` A.
have hV:@open T V:=openI hU hOpen.
have haV:V a by split.
have hDifference:=@norm_analytic_subtract R X R^o NX (fun t=>`|t|) hNX
  (@scalar_absolute_value_norm R) A (value f) (value g) hf hg.
have hZero:forall x,V x ->value f x-value g x=0.
  by move=>x [hx _];rewrite (hValues x hx) subrr.
have hGlobal:=@analytic_identity_open_zero R X R^o NX (fun t=>`|t|) hNX
  (@scalar_absolute_value_norm R) A V (fun x=>value f x-value g x) a
  hConnected hDifference hV haV (fun x hx=>hx.2) hZero.
move=>x hx;apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hGlobal x hx.
Qed.
