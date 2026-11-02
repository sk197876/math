(** Federer (1969), 3.1.13, p. 225:
    partition laws depend on the functions only
    on U. This supports their smooth
    extension by zero to the entire source. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP NormClassHigherLocalValues
  NormPartitionUnityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_partition_domain_agreement]:
    replacing the partition functions by extensions
    that agree on U preserves their partition
    laws, supporting the last assertion in
    Federer 3.1.13, p. 225. *)
Theorem norm_partition_domain_agreement (R : realType)
    (X : lmodType R) (J : choiceType) (NX : X->R)
    (hNX : is_real_norm NX)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (U : X->Prop) (I : J->Prop) (v w : J->X->R) :
  (forall j, I j -> forall x, U x -> v j x=w j x) ->
  is_norm_smooth_partition_of_unity NX ev ZN U I v ->
  is_norm_smooth_partition_of_unity NX ev ZN U I w.
Proof.
move=>he hv; constructor.
- move=>j hj x hx; rewrite -(he j hj x hx); exact: (norm_partition_range hv hj hx).
- move=>j hj k.
  exact: (norm_class_higher_domain_agreement hNX (@scalar_absolute_value_norm R)
    hZ (he j hj) (norm_partition_smooth hv hj k)).
- move=>a ha.
  have [O [hOa [hOU [hOo [F [hFI hF]]]]]] := norm_partition_locally_finite hv ha.
  exists O; split; first exact hOa; split; first exact hOU; split; first exact hOo.
  exists F; split; first exact hFI.
  move=>x hx j hj hn; rewrite -(he j hj x (hOU x hx)); exact: (hF x hx j hj hn).
- move=>x hx F hFI hF.
  have hFv j (hj : I j) (hn : j \notin F) : v j x=0.
    rewrite he //; exact: (hF j hj hn).
  rewrite (norm_partition_sum_one hv hx hFI hFv).
  rewrite !big_seq_fsetE; apply: eq_bigr=>j _.
  exact: (he (val j) (hFI _ (valP j)) x hx).
Qed.
