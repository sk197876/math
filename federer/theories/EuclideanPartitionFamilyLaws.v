(** Federer (1969), 3.1.13, p. 225:
    public support, range and derivative-sum laws
    of the globally extended partition family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness CompactSupportFunctionUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormLocallyFiniteFamilyUP FiniteFamilySumUP NormPartitionUnityUP
  NormPartitionUnityDifferentials EuclideanPartitionBallCoverUP EuclideanPartitionLocalFiniteness
  EuclideanPartitionFamilyUP LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PublicLaws.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N
  (fun t : R^o=>`|t|) (@ev i) (@ZN i).
Variables (Phi : set (set X)) (S : set X) (sigma : X->R) (v : X->X->R).
Hypothesis ho : forall T, Phi T -> open T.
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Hypothesis hf : is_euclidean_partition_family ev ZN Phi S sigma v.
Local Notation U := (\bigcup_(T in Phi) T).

(** Source for [euclidean_partition_global_range]:
    the globally extended v_s take values
    in [0,1], Federer 3.1.13,
    p. 225, including points outside U. *)
Lemma euclidean_partition_global_range s x : S s -> 0<=v s x<=1.
Proof.
move=>hs; case:(pselect (U x))=>[hx|hx].
- exact: (norm_partition_range (partition_family_partition hf) hs hx).
- by rewrite (partition_family_zero_extension hf hs hx) lexx ler01.
Qed.

(** Source for [euclidean_partition_supports_refine]:
    the compact supports of the normalized
    functions refine Phi and are locally
    finite on U, Federer 3.1.13,
    p. 225. The proof uses
    only the abstract support containment laws. *)
Theorem euclidean_partition_supports_refine :
  (forall s, S s -> exists T, Phi T /\ real_function_support (v s) `<=` T) /\
  is_locally_finite_family_on U S (fun s=>real_function_support (v s)).
Proof.
split.
- move=>s hs; have [T [hT hBT]] := partition_tenfold_balls_subordinate hS hs.
  exists T; split; first exact hT.
  exact: (subset_trans (partition_family_support_ball hf hs) hBT).
- exact: (partition_subordinate_supports_locally_finite ho hS
    (fun s hs=>partition_family_support_ball hf hs)).
Qed.

(** Source for [euclidean_partition_derivative_family]:
    positive-order derivative families are locally
    finite and sum to zero on U,
    Federer 3.1.13, p. 225.
    The supplied D is required to be
    the actual global derivative of each
    partition function; its existence follows from
    their proved global class-infinity laws. *)
Theorem euclidean_partition_derivative_family k (D : X->X->Z k.+1) :
  (forall s, S s -> forall x, has_norm_higher_differential N ev ZN
    (fun _=>True) (v s) k.+1 x (D s x)) ->
  is_norm_locally_finite_function_family N U S D /\
  is_finite_family_sum_on U S D (fun _=>0).
Proof.
move=>hD; split.
- exact: (norm_locally_finite_differential_family
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (@scalar_absolute_value_norm R) hZ
    (norm_partition_locally_finite (partition_family_partition hf)) hD).
- exact: (norm_partition_positive_differentials_sum_zero
    (inner_norm_real_norm (@euclidean_inner_productP R m)) hZ
    (partition_family_partition hf) hD).
Qed.
End PublicLaws.
