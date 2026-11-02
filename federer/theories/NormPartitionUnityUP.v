(** Federer (1969), 3.1.13, p. 225:
    intrinsic laws of a smooth partition of unity
    on the open union. Existence and subordination
    are proved separately from these defining laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormClassHigherUP FiniteFamilySumUP NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_norm_smooth_partition_of_unity]:
    the functions v_s form a smooth
    locally finite partition of unity, Federer
    3.1.13, p. 225. Every
    condition is a property to prove of
    a supplied family; no existence is postulated. *)
Record is_norm_smooth_partition_of_unity (R : realType)
    (X : lmodType R) (J : choiceType) (NX : X->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (U : X->Prop) (I : J->Prop) (v : J->X->R) : Prop := {
  (** Source for [norm_partition_range]:
      the partition values lie in [0,1],
      Federer 3.1.13, p. 225. *)
  norm_partition_range : forall j, I j -> forall x, U x -> 0<=v j x<=1;
  (** Source for [norm_partition_smooth]:
      each partition function is of class
      infinity on U, Federer 3.1.13, p. 225. *)
  norm_partition_smooth : forall j, I j ->
    norm_class_infinity NX (fun t : R^o=>`|t|) ev ZN U (v j);
  (** Source for [norm_partition_locally_finite]:
      only finitely many functions can be
      nonzero near any point of U,
      Federer 3.1.13, p. 225. *)
  norm_partition_locally_finite : is_norm_locally_finite_function_family NX U I v;
  (** Source for [norm_partition_sum_one]:
      the locally finite sum equals one,
      Federer 3.1.13, p. 225. *)
  norm_partition_sum_one : is_finite_family_sum_on U I v (fun _=>1)
}.
