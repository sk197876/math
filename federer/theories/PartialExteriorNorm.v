(** Federer (1969), 3.2.20, p. 256: public bounded
    partial exterior norm, accessed only through its opaque least-bound
    laws. Ambient linear representatives establish existence of a bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations PartialFunctionUP
  EuclideanLinearJacobian PartialExteriorNormUP PartialExteriorNormLaws PartialExteriorNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [partial_exterior_norm]: the norm of the actual
    partial exterior graph in Federer 3.2.20, p. 256, with
    the unit-ball supremum convention of 1.7.6, p. 33.
    Its real-supremum implementation is opaque. *)
Definition partial_exterior_norm (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k))
    (hd : exists L : R, 0<=L /\ is_partial_exterior_bound q d L) :=
  @PartialExteriorNorms.value R n k q d hd.

(** Source for [partial_exterior_norm_specification]: the independently
    stated norm laws supporting Federer 3.2.20, p. 256.
    No construction formula is used in downstream proofs. *)
Lemma partial_exterior_norm_specification (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k))
    (hd : exists L : R, 0<=L /\ is_partial_exterior_bound q d L) :
  is_partial_exterior_norm q d (@partial_exterior_norm R n k q d hd).
Proof. exact: PartialExteriorNorms.laws. Qed.

(** Source for [partial_exterior_norm_bounded_exists]: supporting
    bounded-cost existence in Federer 3.2.20, p. 256.
    Expose only the existence and abstract laws of the sealed norm. *)
Theorem partial_exterior_norm_bounded_exists (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k)) :
  (exists L : R, 0<=L /\ is_partial_exterior_bound q d L) ->
  exists J : R, is_partial_exterior_norm q d J.
Proof.
move=> hd; exists (@partial_exterior_norm R n k q d hd).
exact: (@partial_exterior_norm_specification R n k q d hd).
Qed.

(** Source for [partial_exterior_norm_linear_model_exists]: supporting
    existence of the norm in Federer 3.2.20, p. 256.
    The usual ambient exterior norm bounds actual graph words, while
    the chosen partial norm is accessed only through its abstract laws. *)
Theorem partial_exterior_norm_linear_model_exists (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k)) (D : Hom (R_n R n) (R_n R k)) :
  (forall v w, partial_function_graph d v w -> D v=w) ->
  exists J : R, is_partial_exterior_norm q d J.
Proof.
move=> hModel; apply: partial_exterior_norm_bounded_exists.
exists (euclidean_linear_jacobian q D); split.
- exact: euclidean_linear_jacobian_nonnegative.
- exact: partial_exterior_representative_bound hModel.
Qed.
