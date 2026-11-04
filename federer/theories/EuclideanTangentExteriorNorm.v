(** Federer (1969), 3.2.48, pp. 285–286: the intrinsic tangent
    exterior norm of the actual differential. This wrapper uses only
    the existing sealed partial exterior norm of 3.2.20, p. 256.
    It introduces no orientation field or selected tangent frame. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanLinearJacobian PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialExteriorNormUP PartialExteriorNormLaws PartialExteriorNorm TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [tangent_exterior_graph_bound]: a full ambient linear
    differential bounds its actual tangent graph, supporting the intrinsic
    Jacobian of 3.2.48, p. 286. Only the public linear representative
    bound of 3.2.20, p. 256, is used. *)
Lemma tangent_exterior_graph_bound (R:realType) n k q (M:set (R_n R n)) a
    (D:Hom (R_n R n) (R_n R k)):
  exists L:R,0<=L /\is_partial_exterior_bound q
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) M a)
      (partial_function_total D)) L.
Proof.
exists (euclidean_linear_jacobian q D); split; first exact:euclidean_linear_jacobian_nonnegative.
apply:partial_exterior_representative_bound=>v w [hv hw]; exact hw.
Qed.

(** Source for [euclidean_tangent_exterior_norm]: the actual tangent
    exterior norm used in 3.2.48, pp. 285–286. It is the existing
    opaque least nonnegative exterior bound on exactly the original
    tangent graph; no value of a differential off that tangent is tested. *)
Definition euclidean_tangent_exterior_norm (R:realType) n k q (M:set (R_n R n)) a
    (D:Hom (R_n R n) (R_n R k)):=
  @partial_exterior_norm R n k q
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) M a)
      (partial_function_total D)) (@tangent_exterior_graph_bound R n k q M a D).

(** Source for [euclidean_tangent_exterior_normP]: the exact tangent
    exterior norm laws for the actual Jacobian in 3.2.48, p. 286.
    The implementation remains encapsulated by PartialExteriorNorms. *)
Lemma euclidean_tangent_exterior_normP (R:realType) n k q (M:set (R_n R n)) a
    (D:Hom (R_n R n) (R_n R k)):
  is_partial_exterior_norm q
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) M a)
      (partial_function_total D)) (@euclidean_tangent_exterior_norm R n k q M a D).
Proof. exact:partial_exterior_norm_specification. Qed.

(** Source for [euclidean_tangent_exterior_norm_value]: a checked
    tangent-norm calculation identifies the original intrinsic Jacobian
    in 3.2.48, p. 286, by its public least-bound uniqueness law. *)
Lemma euclidean_tangent_exterior_norm_value (R:realType) n k q (M:set (R_n R n)) a
    (D:Hom (R_n R n) (R_n R k)) j:
  is_partial_exterior_norm q
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) M a)
      (partial_function_total D)) j ->
  @euclidean_tangent_exterior_norm R n k q M a D=j.
Proof. move=>hj; exact (partial_exterior_norm_unique (euclidean_tangent_exterior_normP q M a D) hj). Qed.
