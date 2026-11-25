(** Federer (1969), 3.4.5, p. 319: supporting the
    absence of proper zero divisors by the analytic identity
    argument already proved in 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormBoundedLinearTopology ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialConstant NormHigherDifferentialLocal NormHigherDifferentialUnique
  NormAnalyticUP NormAnalyticLocal NormAnalyticFlatIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_identity_open_zero]: a supporting
    identity theorem for the no-zero-divisor assertion of
    3.4.5, p. 319. An analytic function on a
    connected domain, zero on a nonempty open subset, is
    zero everywhere on its original domain. Locality gives
    zero actual jets at one point, then 3.1.24 applies. *)
Theorem analytic_identity_open_zero (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A U:set X) (f:X->Y) (b:X):
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X Y NX NY hNX hNY A f ->
  @open (real_norm_metric_space hNX) U ->U b ->U `<=` A ->
  (forall x,U x ->f x=0) ->forall x,A x ->f x=0.
Proof.
move=>hConnected hAnalytic hU hb hUA hZero.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
have hZ i:is_continuous_multilinear_space NX NY (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
have hSmooth:=norm_analytic_class_all_orders hAnalytic.
have hA x (hx:A x):norm_domain_interior NX A x:=((hSmooth 0%N).1 x hx).1.
have hOpen x (hx:U x):norm_domain_interior NX U x.
  rewrite openE in hU;exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hU x hx)).
apply:(@norm_analytic_flat_identity R X Y NX NY hNX hNY A f b
  hConnected hAnalytic (hUA b hb))=>m z hz.
have hC:=@norm_higher_differential_constant R X Y NX NY hNX hNY Z ev ZN hZ
  A hA 0 (0:Z 0%N) (linear0 _) m b (hUA b hb).
have hForm k:@constant_higher_form R Z (0:Z 0%N) k=0 by case:k.
rewrite (hForm m) in hC.
have hEquivalent:=@norm_higher_differential_local_agreement R X Y NX NY hNX hNY Z ev ZN hZ
  m A A U f (fun _=>0) hOpen (fun x hx=>iff_refl _) (fun x hx _=>hZero x hx) b hb z.
exact:(@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ
  A (fun _=>0) m b z 0 (hEquivalent.1 hz) hC).
Qed.
