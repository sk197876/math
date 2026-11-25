(** Federer (1969), 4.1.3, p. 348: the original coordinate
    product of one-variable tests vanishes outside a compact
    Euclidean ball. Dimension zero has empty product one on R^0,
    whose whole source is compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SmoothCompactSet SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation TestLineSupportBound EuclideanCoordinateLoneBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [test_coordinate_product_support_bound]: an actual
    finite ball bounds the nonzero coordinate product, supporting
    the tensor image in Federer 4.1.3, p. 348. *)
Theorem test_coordinate_product_support_bound (R:realType) n (A:lmodType R)
    (av:A->R^o->R^o)
    (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
      (@scalar_absolute_value_norm R) (fun _=>True) av)
    (f:'I_n->smooth_test_space hA):
  exists b:R,0<=b /\ forall x:R_n R n,
    b<inner_norm (@euclidean_inner_productP R n) x ->
    \prod_i smooth_test_value hA (f i) (x i)=0.
Proof.
have hFor i:=@test_line_nonzero_argument_bound R A av hA (f i).
have[b hb]:=choice hFor.
exists (\sum_i b i); split.
- apply:sumr_ge0=>i _; exact:ltW (hb i).1.
- move=>x hx; case:(eqVneq (\prod_i smooth_test_value hA (f i) (x i)) 0)=>[hZero|hNonzero]; first exact hZero.
  exfalso.
  have hEach i:smooth_test_value hA (f i) (x i)<>0.
    move=>hZero.
    have hP: \prod_j smooth_test_value hA (f j) (x j)=0.
      by rewrite (bigD1 i) //= hZero mul0r.
    by move:hNonzero; rewrite hP eqxx.
  have hBound:inner_norm (@euclidean_inner_productP R n) x<=\sum_i b i.
    apply:le_trans (euclidean_coordinate_lone_bound x) _.
    apply:ler_sum=>i _; exact:(hb i).2 (x i) (hEach i).
  have hContra:=lt_le_trans hx hBound.
  by move:hContra; rewrite ltxx.
Qed.
