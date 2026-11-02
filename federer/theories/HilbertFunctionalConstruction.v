(** Federer (1969), 1.7.13, p. 37: existence of the inner-product
    representative of a continuous linear functional. For nonzero f the
    proof projects a point with f(a)= 1 onto ker(f), exactly as in the book.
    The zero functional is handled separately. Source context and supporting
    nearest-point reference: HilbertSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From mathcomp Require Import classical_sets topology num_normedtype normed_module.
From Federer Require Import ModuleQuotient InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology InnerNearestUP InnerNearestSubspace InnerConvex
  HilbertSpaceUP HilbertNearest HilbertFunctionalUP LinearFunctionalKernel
  HilbertFunctionalFormula Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hilbert_functional_vector_exists]: Federer
    1.7.13, p. 37, final assertion, existence: each continuous
    linear functional is inner product with a vector, without a
    finite-dimensional restriction. *)
Theorem hilbert_functional_vector_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
    (f : {linear V -> R^o})
    (hf : continuous (fun x : inner_metric_space hB => (f x : R^o))) :
    exists u, is_hilbert_functional_vector B f u.
Proof.
case: (pselect (exists v, f v != 0)) => [[v hv]|hzero]; last first.
  exists 0 => x; rewrite (bil0l (inner_bilinear hB)).
  apply/eqP; apply/negPn/negP=> hx; apply: hzero; by exists x.
pose a := (f v)^-1 *: v.
have ha : f a= 1 := linear_functional_value_one hv.
pose S := linear_functional_kernel f.
have hn : (S : set (inner_metric_space hB)) !=set0 by exists 0; exact: subspace_zero.
have hs : closed (S : set (inner_metric_space hB)) := linear_functional_kernel_closed hf.
have hvx : is_inner_convex (S : set (inner_metric_space hB)).
  move=> x y hx hy t _ _; exact (@inner_subspace_convex R V S x y hx hy t).
pose c := @hilbert_nearest R V B hB hH a S hn hs hvx.
have hc : is_inner_nearest hB a S c := @hilbert_nearestP R V B hB hH a S hn hs hvx.
have hfc : f c= 0 := inner_nearest_member_law hc.
exists ((inner_norm hB (a-c)^+2)^-1 *: (a-c)).
apply: (@hilbert_functional_residual_formula R V B hB f a c ha hfc) => x hx.
exact (@inner_nearest_subspace_orthogonal R V B hB S a c hc x hx).
Qed.
