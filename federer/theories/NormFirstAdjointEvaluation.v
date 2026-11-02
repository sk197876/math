(** Federer (1969), 3.1.21, p. 234: adjoint derivative
    evaluation in normal-bundle coordinates preserves class k. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne
  NormOperatorNormUP NormBoundedBilinearUP NormRegularity NormRegularityBilinear
  EuclideanAdjoint EuclideanAdjointBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Evaluation.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable Z:lmodType R.
Variable ev:{ffun 'I_1->X}->Hom Z X.
Variable ZN:Z->R.
Hypothesis hZ:is_continuous_multilinear_space NX NX ev ZN.
Local Notation op := (@continuous_multilinear_one_operator R X X Z NX NX ev ZN hZ).
Local Notation ad := (@euclidean_adjoint R n).

(** Source for [norm_first_adjoint_bounded_bilinear]: supporting
    (operator,vector) -> operator-adjoint(vector) in the normal
    bundle assertion of Federer 3.1.21, p. 234.
    The operator space is abstract; the adjoint is used only
    through its existing sealed pairing and norm laws. *)
Lemma norm_first_adjoint_bounded_bilinear :
  norm_bounded_bilinear ZN NX NX (fun z v=>ad (op z) v).
Proof.
split.
- split.
  + move=>v c z w.
    have ho:op (c*:z+w)=c*:op z+op w.
      exact (@continuous_multilinear_one_operator_linear R X X Z NX NX ev ZN hZ c z w).
    rewrite ho (@euclidean_adjoint_linear R n c (op z) (op w)).
    by [].
  + move=>z c x y; exact: linearP.
- exists 1; split; first exact: ler01.
  move=>z v; rewrite mul1r.
  have hN:=@continuous_multilinear_one_norm_laws R X X Z NX NX ev ZN hZ z.
  exact (@euclidean_adjoint_same_bound R n (op z) (ZN z)
    (norm_operator_nonnegative hN) (norm_operator_bound hN) v).
Qed.

(** Source for [norm_class_first_adjoint_evaluation]: supporting
    class-(k-1) regularity of normal-bundle coordinate changes,
    Federer 3.1.21, p. 234. Both operator and vector
    arguments vary, without an additional continuity premise. *)
Lemma norm_class_first_adjoint_evaluation (P:lmodType R) (NP:P->R)
    (hNP:is_real_norm NP) (A:P->Prop) (F:P->Z) (V:P->X) k :
  norm_class hNP (continuous_multilinear_norm_is_norm
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hZ) A F k ->
  norm_class hNP (inner_norm_real_norm (@euclidean_inner_productP R n)) A V k ->
  norm_class hNP (inner_norm_real_norm (@euclidean_inner_productP R n)) A
    (fun x=>ad (op (F x)) (V x)) k.
Proof.
move=>hF hV; exact: norm_class_bilinear norm_first_adjoint_bounded_bilinear hF hV.
Qed.
End Evaluation.
