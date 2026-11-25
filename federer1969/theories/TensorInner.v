(** Federer (1969), 1.7.9, p. 35: public tensor inner product and norm,
    obtained from the sealed specification. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm TensorUP TensorProduct
  TensorInnerUP TensorInnerSealed TensorInnerPositivity OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Interface.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.

(** Source for [tensor_inner]: Federer 1.7.9, p. 35,
    the characterised tensor inner product from its sealed interface. *)
Definition tensor_inner := @TensorInner.product R V W B C hB hC.

(** Source for [tensor_innerP]: Federer 1.7.9, p. 35,
    the public product satisfies its abstract defining laws. *)
Lemma tensor_innerP : is_tensor_inner_product B C tensor_inner.
Proof. exact: TensorInner.laws. Qed.

(** Source for [tensor_inner_productP]: Federer 1.7.9,
    p. 35, the specified form is an inner product. *)
Theorem tensor_inner_productP : is_inner_product tensor_inner.
Proof. exact: tensor_inner_laws tensor_innerP. Qed.

(** Source for [tensor_innerE]: Federer 1.7.9, p. 35,
    the defining pure-tensor formula, with the prime on w' restored
    at erratum p. 1, book p. 35 line 3. *)
Theorem tensor_innerE v w v' w' :
  tensor_inner (tensor_inj v w) (tensor_inj v' w') = B v v' * C w w'.
Proof. exact (@tensor_inner_pure R V W B C tensor_inner tensor_innerP v w v' w'). Qed.

(** Source for [tensor_inner_orthonormal]: Federer 1.7.9,
    p. 35, the pairwise pure tensors of two orthonormal families
    form an orthonormal family in the tensor space. *)
Theorem tensor_inner_orthonormal (I J : finType) (e : I -> V) (f : J -> W)
    (he : orthonormal_family B e) (hf : orthonormal_family C f) :
  orthonormal_family tensor_inner (fun ij : (I * J)%type => tensor_inj (e ij.1) (f ij.2)).
Proof. exact (@tensor_pure_orthonormal R V W B C tensor_inner tensor_innerE I J e f he hf). Qed.

(** Source for [tensor_norm]: Federer 1.7.9, p. 35,
    the length associated with the induced tensor inner product. *)
Definition tensor_norm := inner_norm tensor_inner_productP.

(** Source for [tensor_norm_pure]: Federer 1.7.9,
    p. 35, supporting consequence of the defining equation:
    the norm of a pure tensor is the product of the factor norms. *)
Theorem tensor_norm_pure v w :
  tensor_norm (tensor_inj v w) = inner_norm hB v * inner_norm hC w.
Proof.
apply: inner_norm_value.
- exact: mulr_ge0 (inner_norm_nonnegative hB v) (inner_norm_nonnegative hC w).
- by rewrite exprMn !inner_norm_sqr tensor_innerE.
Qed.
End Interface.
