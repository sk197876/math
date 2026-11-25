(** Federer (1969), 4.1.8, p. 360: the
    coordinate pure tests used in 4.1.3, p. 348,
    factor across the original two Euclidean blocks. The
    empty coordinate product retains its value one. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness EuclideanBlockCoordinates SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_test_block_product]: splitting
    a pure coordinate scalar product into its first and
    last blocks gives the product of the two factor
    tests, supporting Federer 4.1.8, p. 360.
    The proof uses the original block-coordinate cancellation. *)
Theorem coordinate_test_block_product (R:realType) m n
    (A:lmodType R) (av:A->R^o->R^o)
    (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
      (@scalar_absolute_value_norm R) (fun _=>True) av)
    (f:'I_(m+n)->smooth_test_space hA) (a:R_n R m) (b:R_n R n):
  (\prod_t smooth_test_value hA (f t) (@euclidean_block_join R m n (a,b) t))=
    (\prod_s smooth_test_value hA (f (lshift n s)) (a s))*
      (\prod_t smooth_test_value hA (f (rshift m t)) (b t)).
Proof.
rewrite big_split_ord.
congr (_*_);apply:eq_bigr=>t _;
  by rewrite ?euclidean_block_join_left ?euclidean_block_join_right.
Qed.
