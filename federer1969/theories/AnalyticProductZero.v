(** Federer (1969), 3.4.5, p. 319: supporting
    the no-zero-divisor assertion for analytic function germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormAnalyticUP NormAnalyticLocal
  NormClassZeroNonzeroLocus AnalyticIdentityOpenZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_product_zero_connected]: the local
    no-zero-divisor inference of 3.4.5, p. 319,
    expanded through the identity theorem of 3.1.24. A product
    of two actual analytic scalar functions is zero on a connected
    domain only if one factor is identically zero there. *)
Theorem analytic_product_zero_connected (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (f g:X->R):
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A f ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A g ->
  (forall x,A x ->f x*g x=0) ->
  (forall x,A x ->f x=0) \/(forall x,A x ->g x=0).
Proof.
move=>hConnected hf hg hProduct.
case:(pselect (exists b,A b /\ f b!=0))=>[[b [hb hNonzero]]|hNone].
- right.
  pose U:=fun x=>A x /\f x!=0.
  have hU:@open (real_norm_metric_space hNX) U.
    exact:(@norm_class_zero_nonzero_locus_open R X R^o NX (fun t=>`|t|)
      hNX (@scalar_absolute_value_norm R) A f
      (norm_class_continuous (norm_analytic_class_all_orders hf 0%N))).
  apply:(@analytic_identity_open_zero R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    A U g b hConnected hg hU (conj hb hNonzero) (fun x hx=>hx.1))=>x hx.
  apply/eqP;move/eqP:(hProduct x hx.1).
  by rewrite mulf_eq0 (negbTE hx.2) orFb.
- left=>x hx;case:(eqVneq (f x) 0)=>[hZero|hNonzero];first exact:hZero.
  exfalso;apply:hNone;exists x;by split.
Qed.
