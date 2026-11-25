(** Federer (1969), 4.1.3, p. 348: products of actual
    one-variable test functions are smooth on R^n. Only the
    previously proved coordinate linear maps and bounded
    bilinear calculus of 3.1.11 are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormRegularity NormRegularityOperations
  NormRegularityLinearMaps NormRegularityBilinear EuclideanScalarCoordinateMaps
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestCoordinateProductSmooth.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Variable f:'I_n->smooth_test_space hA.

(** Source for [test_coordinate_product_smooth]: the original
    finite coordinate product defines a smooth scalar function,
    supporting the tensor map in Federer 4.1.3, p. 348. *)
Theorem test_coordinate_product_smooth:
  norm_class_all_orders hN hR (fun _=>True)
    (fun x:X=>(\prod_i smooth_test_value hA (f i) (x i):R^o)).
Proof.
move=>k.
have hOne: norm_class hN hR (fun _=>True) (fun _:X=>(1:R^o)) k.
  apply:norm_class_constant=>x _; exact:norm_full_domain_interior.
have hEach i:norm_class hN hR (fun _=>True)
    (fun x:X=>smooth_test_value hA (f i) (x i)) k.
  exact:(@norm_class_precompose_linear R X R^o R^o N (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    hN hR hR (fun _=>True) (smooth_test_value hA (f i))
    (euclidean_scalar_coordinate_map i) k (euclidean_scalar_coordinate_bounded i)
    (smooth_test_value_smooth hA (f i) k)).
have hSeq (s:seq 'I_n):norm_class hN hR (fun _=>True)
    (fun x:X=>(\prod_(i<-s) smooth_test_value hA (f i) (x i):R^o)) k.
  elim:s=>[|i s hs].
  - have hEq:(fun x:X=>(\prod_(i<-[::]) smooth_test_value hA (f i) (x i):R^o))=(fun _:X=>(1:R^o)).
      apply:funext=>x; by rewrite big_nil.
    by rewrite hEq.
  - have hProduct:=norm_class_scalar_product (hEach i) hs.
    have hEq:(fun x:X=>smooth_test_value hA (f i) (x i)*:
        (\prod_(j<-s) smooth_test_value hA (f j) (x j):R^o))=
      (fun x:X=>(\prod_(j<-i::s) smooth_test_value hA (f j) (x j):R^o)).
      apply:funext=>x; by rewrite big_cons.
    by rewrite -hEq; exact hProduct.
exact:(hSeq (index_enum 'I_n)).
Qed.
End TestCoordinateProductSmooth.
