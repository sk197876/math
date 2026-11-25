(** Federer (1969), 3.4.5, p. 320: analytic
    subvarieties specified by finite original equations on an
    open domain. An indexed finite list permits repeated
    equations and includes the empty system. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_finite_analytic_variety]: var(U,F),
    3.4.5, p. 320. The domain is open,
    all defining functions are actually analytic there, and
    membership is exactly simultaneous vanishing. *)
Definition is_finite_analytic_variety (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U S:set X):Prop:=
  @open (real_norm_metric_space hNX) U /\exists I:finType,exists f:I->X->R,
    (forall i,@norm_analytic R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R) U (f i)) /\
    forall x,S x <->U x /\forall i,f i x=0.

(** Source for [is_original_zero_set]: the independent
    membership law of var(U,F), 3.4.5, p. 320.
    Existence is separate from this specification. *)
Record is_original_zero_set (A:zmodType) (X:Type) (U:set X) (I:finType) (f:I->X->A) (S:set X):Prop:={
  (** Source for [original_zero_set_membership]: original
      domain and every equation must hold, 3.4.5, p. 320. *)
  original_zero_set_membership:forall x,S x <->U x /\forall i,f i x=0
}.
