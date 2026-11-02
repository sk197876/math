(** Federer (1969), 3.1.13, pp. 224–225:
    abstract laws of the denominator and normalized
    smooth family associated with the selected balls.
    Quantitative higher-derivative bounds are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  CompactSupportFunctionUP MetricClosedBalls ContinuousMultilinearUP NormClassHigherUP
  FiniteFamilySumUP NormPartitionUnityUP FedererCoverRadius EuclideanPartitionBumps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FamilySpecification.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o.
Variable ZN : forall i, Z i->R.
Variables (Phi : set (set X)) (S : set X).
Local Notation U := (\bigcup_(T in Phi) T).

(** Source for [is_euclidean_partition_family]:
    sigma and the globally extended normalized
    functions v_s in Federer 3.1.13,
    p. 225. This specification
    records their qualitative laws; it does
    not assert the later quantitative estimates. *)
Record is_euclidean_partition_family (sigma : X->R) (v : X->X->R) : Prop := {
  (** Source for [partition_family_denominator_sum]:
      sigma=sum_s u_s on U, Federer 3.1.13, p. 225. *)
  partition_family_denominator_sum :
    is_finite_family_sum_on U S (euclidean_partition_bump Phi) sigma;
  (** Source for [partition_family_denominator_lower]:
      sigma(x)>=1 on U, Federer 3.1.13, p. 225. *)
  partition_family_denominator_lower : forall x, U x -> 1<=sigma x;
  (** Source for [partition_family_denominator_smooth]:
      sigma is smooth on U, Federer 3.1.13, p. 225. *)
  partition_family_denominator_smooth :
    norm_class_infinity N (fun t : R^o=>`|t|) ev ZN U sigma;
  (** Source for [partition_family_normalization]:
      v_s=u_s/sigma on U, Federer 3.1.13, p. 225. *)
  partition_family_normalization : forall s, S s -> forall x, U x ->
    v s x=euclidean_partition_bump Phi s x/sigma x;
  (** Source for [partition_family_zero_extension]:
      v_s has value zero off U,
      Federer 3.1.13, p. 225. *)
  partition_family_zero_extension : forall s, S s -> forall x, ~U x -> v s x=0;
  (** Source for [partition_family_partition]:
      the v_s are a smooth locally
      finite partition of unity on U,
      Federer 3.1.13, p. 225. *)
  partition_family_partition : is_norm_smooth_partition_of_unity N ev ZN U S v;
  (** Source for [partition_family_global_smooth]:
      each v_s is smooth on all R^m,
      Federer 3.1.13, p. 225. *)
  partition_family_global_smooth : forall s, S s ->
    norm_class_infinity N (fun t : R^o=>`|t|) ev ZN (fun _=>True) (v s);
  (** Source for [partition_family_support_ball]:
      the supports remain in B[s,10h(s)],
      supporting the refinement in Federer
      3.1.13, pp. 224–225. *)
  partition_family_support_ball : forall s, S s ->
    real_function_support (v s) `<=` metric_closed_ball s (10*federer_cover_radius Phi s);
  (** Source for [partition_family_compact_support]:
      every v_s has compact support,
      Federer 3.1.13, pp. 224–225. *)
  partition_family_compact_support : forall s, S s -> compact (real_function_support (v s))
}.
End FamilySpecification.
