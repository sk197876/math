(** Federer (1969), 3.2.28(1), printed p. 263: the actual
    Gram differential and its continuous field for the
    Hilbert inner-product norms prescribed in 1.7.9. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness
  HomCompositionDeterminant EuclideanHomOperator EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra EuclideanGramSmooth
  NormDifferentialUP NormClassOneUP NormRegularity NormDifferentialDirectional
  FiniteNormDifferentialTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section InnerDifferential.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation Y:=(Hom (R_n R m) (R_n R m)).
Local Notation NX:=(inner_norm (@euclidean_hom_inner_productP R m n)).
Local Notation NY:=(inner_norm (@euclidean_hom_inner_productP R m m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_hom_inner_productP R m n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_hom_inner_productP R m m)).

(** Source for [euclidean_gram_inner_has_differential]:
    DP(g)h=h* g+g* h for the actual Hom Hilbert
    norms, Federer 3.2.28(1), p. 263. Equivalent
    finite-dimensional norms preserve the full remainder law. *)
Theorem euclidean_gram_inner_has_differential (g:X):
  has_norm_differential NX NY (fun _=>True) (@euclidean_gram_map R m n)
    g (euclidean_gram_differential g).
Proof.
apply:(@norm_differential_finite_norm_change R X Y
  (@euclidean_operator_norm R m n) NX (@euclidean_operator_norm R m m) NY
  (@euclidean_operator_norm_is_norm R m n) hNX
  (@euclidean_operator_norm_is_norm R m m) hNY _ _
  (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R n) (@coordinate_basisP R n)) _ _
  (@hom_rank_one_baseP R (R_n R m) (R_n R m) m m
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R m) (@coordinate_basisP R m))).
exact:euclidean_gram_has_differential.
Qed.

(** Source for [euclidean_gram_inner_class_one_field]: the
    displayed continuous Gram differential field in the actual
    Euclidean ambient metric, Federer 3.2.28(1), p. 263. *)
Theorem euclidean_gram_inner_class_one_field:
  is_norm_class_one_field NX NY (fun _=>True) (@euclidean_gram_map R m n)
    (@euclidean_gram_differential R m n).
Proof.
have [D hD]:=(norm_class_firstP hNX hNY (fun _=>True)
  (@euclidean_gram_map R m n)).1 (@euclidean_gram_inner_smooth R m n 1%N).
have hEq:D=@euclidean_gram_differential R m n.
  apply:funext=>g.
  exact:(norm_differential_unique hNX hNY
    (norm_class_one_differential hD I) (euclidean_gram_inner_has_differential g)).
by rewrite -hEq.
Qed.
End InnerDifferential.
