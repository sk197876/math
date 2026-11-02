(** Federer (1969), 1.7.9, p. 35: the operator norm is at most the norm of
    the associated tensor. The proof applies the already proved Cauchy
    inequality on the tensor space, rather than coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  InnerNormalization InnerPolarity InnerDual TensorProduct TensorInner
  TensorInnerEvaluation HomInner Hom Gamma LinearBasis OperatorNormUP OperatorNormAdjoint AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hom_norm_vector_bound]: Federer 1.7.9,
    p. 35, supporting homogeneous estimate: the norm of f(x)
    is at most the tensor norm of f times the norm of x. *)
Theorem hom_norm_vector_bound (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (f : Hom V W) x :
  inner_norm hC (f x) <= hom_norm hB hC he f * inner_norm hB x.
Proof.
have [hz|hz] := eqVneq (f x) 0.
- rewrite hz inner_norm0; exact: mulr_ge0 (inner_norm_nonnegative _ _) (inner_norm_nonnegative _ _).
pose y := inner_normalize hC (f x).
have hh := @inner_cauchy_upper R _ _
  (tensor_inner_productP (inner_dual_productP hB he) hC)
  (@Gamma R V W (Finite.clone 'I_n _) e he f)
  (tensor_inj (inner_polarity hB x) y).
rewrite tensor_inner_evaluation GammaK in hh.
change (is_true (C (f x) y <=
  tensor_norm (inner_dual_productP hB he) hC (@Gamma R V W (Finite.clone 'I_n _) e he f) *
  tensor_norm (inner_dual_productP hB he) hC (tensor_inj (inner_polarity hB x) y))) in hh.
rewrite tensor_norm_pure -hom_norm_tensor in hh.
change (is_true (C (f x) y <= hom_norm hB hC he f *
  (inner_dual_norm hB he (inner_polarity hB x) * inner_norm hC y))) in hh.
by rewrite inner_dual_norm_polarity /y inner_normalized_pairing inner_normalize_norm // mulr1 in hh.
Qed.

(** Source for [operator_norm_le_hom_norm]: Federer 1.7.9,
    p. 35, first printed inequality: operator norm is at most the
    norm of the map as an element of Hom(V,W). This statement
    uses the abstract operator-norm laws and includes dimension zero. *)
Theorem operator_norm_le_hom_norm (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (f : Hom V W) L :
  is_operator_norm hB hC (hom_as_linear f) L -> L <= hom_norm hB hC he f.
Proof.
move=> hL; have [x [hx <-]] := operator_norm_attained hL.
change (is_true (inner_norm hC (f x) <= hom_norm hB hC he f)).
apply: le_trans (@hom_norm_vector_bound R V W B C hB hC n e he f x) _.
rewrite -[leRHS]mulr1; apply: ler_wpM2l; first exact: inner_norm_nonnegative.
exact hx.
Qed.
