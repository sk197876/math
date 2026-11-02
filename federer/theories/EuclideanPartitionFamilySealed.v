(** Opaque denominator and normalized partition family
    for Federer (1969), 3.1.13, pp. 224–225.
    Only the abstract qualitative laws are exposed;
    quantitative derivative bounds are proved downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  ContinuousMultilinearUP EuclideanPartitionBallCoverUP
  EuclideanPartitionFamilyUP EuclideanPartitionFamilyConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type EuclideanPartitionFamilySignature.
(** Source for [denominator]: sigma=sum_s u_s,
    Federer 3.1.13, p. 225. *)
Parameter denominator : forall (R : realType) (m : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (ho : forall T, Phi T -> open T)
    (hS : is_federer_partition_ball_cover Phi S),
  inner_metric_space (@euclidean_inner_productP R m)->R.
(** Source for [functions]: the normalized functions
    v_s and their global zero extensions,
    Federer 3.1.13, p. 225. *)
Parameter functions : forall (R : realType) (m : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (ho : forall T, Phi T -> open T)
    (hS : is_federer_partition_ball_cover Phi S),
  inner_metric_space (@euclidean_inner_productP R m)->
  inner_metric_space (@euclidean_inner_productP R m)->R.
(** Source for [laws]: the denominator and
    normalized family satisfy their proved smoothness,
    support and partition laws, Federer
    3.1.13, pp. 224–225. *)
Parameter laws : forall (R : realType) (m : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (ho : forall T, Phi T -> open T)
    (hS : is_federer_partition_ball_cover Phi S), is_euclidean_partition_family ev ZN Phi S
    (@denominator R m Z ev ZN hZ Phi S ho hS) (@functions R m Z ev ZN hZ Phi S ho hS).
End EuclideanPartitionFamilySignature.

Module EuclideanPartitionFamily : EuclideanPartitionFamilySignature.
(** Source for [denominator]: choice from the
    privately proved existence of sigma and
    v_s, Federer 3.1.13, p. 225. *)
Definition denominator (R : realType) (m : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (ho : forall T, Phi T -> open T)
    (hS : is_federer_partition_ball_cover Phi S) :
    inner_metric_space (@euclidean_inner_productP R m)->R :=
  projT1 (cid (@euclidean_partition_family_exists R m Z ev ZN hZ Phi S ho hS)).
(** Source for [functions]: choice of the
    same proved family paired with sigma,
    Federer 3.1.13, p. 225. *)
Definition functions (R : realType) (m : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (ho : forall T, Phi T -> open T)
    (hS : is_federer_partition_ball_cover Phi S) :
    inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R m)->R :=
  projT1 (cid (projT2 (cid (@euclidean_partition_family_exists R m Z ev ZN hZ Phi S ho hS)))).
(** Source for [laws]: proof of the
    exposed partition-family specification, Federer
    3.1.13, pp. 224–225. *)
Lemma laws (R : realType) (m : nat)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (ho : forall T, Phi T -> open T)
    (hS : is_federer_partition_ball_cover Phi S) : is_euclidean_partition_family ev ZN Phi S
    (@denominator R m Z ev ZN hZ Phi S ho hS) (@functions R m Z ev ZN hZ Phi S ho hS).
Proof.
exact: (projT2 (cid (projT2 (cid (@euclidean_partition_family_exists R m Z ev ZN hZ Phi S ho hS))))).
Qed.
End EuclideanPartitionFamily.
