(** Federer (1969), 4.1.8, p. 360: the separated
    product pairing uses the original direct-sum exterior map
    from 1.3.2, p. 14, and diagonal from 1.3.3,
    pp. 15–16. This supporting identity relates those existing
    maps without constructing a new exterior algebra. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Tensor TensorUP TensorMaps UnitalGradedTensor
  ExteriorAlgebra ExteriorGrading ExteriorMaps ExteriorDirectSum ExteriorDiagonal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ExteriorBlockDiagonal.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variables V P Q:lmodType K.
Variables (f:{linear V->P}) (g:{linear V->Q}).
Local Notation EV := (exterior_unital V).
Local Notation EP := (exterior_unital P).
Local Notation EQ := (exterior_unital Q).
Local Notation F := (exterior_algebra_map f).
Local Notation G := (exterior_algebra_map g).

(** Source for [exterior_diagonal_block_map]: the original
    block map alpha is the diagonal followed by the two
    exterior projection maps, supporting Federer 4.1.8,
    p. 360, by 1.3.2–3, pp. 14–16.
    The statement holds on the full exterior algebra. *)
Theorem exterior_diagonal_block_map x:
  tensor_map F G (Psi h2 V x)=@ExteriorDirectSum.alpha K h2 V P Q f g x.
Proof.
pose TF:=@unital_tensor_map K EV EV EP EQ F G
  (@exterior_algebra_map_graded K V P f) (@exterior_algebra_map_graded K V Q g) true.
apply:(@alpha_unique K h2 V P Q f g (algebra_comp TF (Psi h2 V))) x=>v.
change (tensor_map F G (Psi h2 V (exterior_generator v))=
  tensor_inj (exterior_generator (f v)) (exterior_unit Q)+
    tensor_inj (exterior_unit P) (exterior_generator (g v))).
by rewrite PsiE linearD !tensor_mapE !exterior_algebra_mapE !algebra_map_one.
Qed.
End ExteriorBlockDiagonal.
