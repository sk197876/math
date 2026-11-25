(** Federer (1969), 3.2.47–48, pp. 282–286:
    composition of the actual Hom operators is a bounded bilinear
    operation for the Hilbert norms. The bound is derived from
    1.7.6 and 1.7.9, pp. 33–35; it is not an
    extra local-chart hypothesis. No sharp constant is needed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm HomInner HomOperatorNorm HomSpaceTopology
  EuclideanHomInnerCharts EuclideanHomOperator EuclideanGramDifferentialAlgebra
  NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hilbert_hom_normE]: the actual
    Frobenius norm used in 3.2.47–48 is the Hom
    norm of 1.7.9, p. 35, independently of the
    proof term furnishing its inner-product laws. *)
Lemma euclidean_hilbert_hom_normE (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  inner_norm (@euclidean_hom_inner_productP R m n) g=
    hom_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
      (@coordinate_basisP R m) g.
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
by rewrite !inner_norm_sqr.
Qed.

(** Source for [euclidean_operator_le_hilbert_norm]: the first
    inequality of 1.7.9, p. 35, specialized to
    the actual metric in 3.2.47–48, pp. 282–286. *)
Lemma euclidean_operator_le_hilbert_norm (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  euclidean_operator_norm g<=inner_norm (@euclidean_hom_inner_productP R m n) g.
Proof.
rewrite euclidean_hilbert_hom_normE.
exact ((hom_operator_norm_comparison (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R m) g).1).
Qed.

(** Source for [euclidean_hilbert_le_dimension_operator_norm]: the
    second inequality of 1.7.9, p. 35, supporting
    actual product-chart regularity in 3.2.47–48. Empty
    source dimensions are retained. *)
Lemma euclidean_hilbert_le_dimension_operator_norm (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  inner_norm (@euclidean_hom_inner_productP R m n) g<=
    Num.sqrt m%:R*euclidean_operator_norm g.
Proof.
rewrite euclidean_hilbert_hom_normE.
exact ((hom_operator_norm_comparison (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R m) g).2).
Qed.

(** Source for [euclidean_composition_hilbert_bound]: composition
    has a finite homogeneous product bound for the actual
    Hilbert metrics, supporting both actual transformation maps
    of 3.2.47–48, pp. 282–286. *)
Theorem euclidean_composition_hilbert_bound (R:realType) a b c
    (f:Hom (R_n R b) (R_n R c)) (g:Hom (R_n R a) (R_n R b)):
  inner_norm (@euclidean_hom_inner_productP R a c) (hom_comp f g)<=
    Num.sqrt a%:R*(inner_norm (@euclidean_hom_inner_productP R b c) f*
      inner_norm (@euclidean_hom_inner_productP R a b) g).
Proof.
apply:le_trans (euclidean_hilbert_le_dimension_operator_norm (hom_comp f g)) _.
apply:ler_wpM2l; first exact:sqrtr_ge0.
apply:le_trans (euclidean_composition_operator_bound f g) _.
apply:ler_pM.
- exact:hom_operator_norm_nonnegative.
- exact:hom_operator_norm_nonnegative.
- exact:euclidean_operator_le_hilbert_norm.
- exact:euclidean_operator_le_hilbert_norm.
Qed.

(** Source for [euclidean_composition_hilbert_bilinear]: the actual
    multiplication used in the local chart and in Psi is
    a bounded bilinear operation, as used through 3.1.11
    in 3.2.47–48, pp. 282–285. *)
Theorem euclidean_composition_hilbert_bilinear (R:realType) a b c:
  norm_bounded_bilinear
    (inner_norm (@euclidean_hom_inner_productP R b c))
    (inner_norm (@euclidean_hom_inner_productP R a b))
    (inner_norm (@euclidean_hom_inner_productP R a c)) (@hom_comp R _ _ _).
Proof.
split.
- split; first by move=>g; exact:hom_precompose_linear.
  move=>f; exact:hom_postcompose_linear.
- exists (Num.sqrt a%:R); split; first exact:sqrtr_ge0.
  exact:euclidean_composition_hilbert_bound.
Qed.
