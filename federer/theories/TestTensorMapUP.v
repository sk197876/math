(** Federer (1969), 4.1.3, p. 348: independent specification
    of the canonical map from [tensor_n D(R,R)] tensor Y to
    D(R^n,Y). The formula on pure tensors precedes construction,
    existence and opaque sealing. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_test_tensor_map]: the original coordinate
    product formula for the tensor image in Federer 4.1.3,
    p. 348, for actual test spaces and arbitrary tensor carriers. *)
Definition is_test_tensor_map (R:realType) n (A:lmodType R)
    (av:A->R^o->R^o)
    (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
      (@scalar_absolute_value_norm R) (fun _=>True) av)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
      hNY (fun _=>True) ev)
    (T W:lmodType R) (mu:{dffun forall i:'I_n,smooth_test_space hA}->T)
    (nu:T->Y->W) (F:Hom W (smooth_test_space hE)):Prop:=
  forall f y x,smooth_test_value hE (F (nu (mu f) y)) x=
    (\prod_i smooth_test_value hA (f i) (x i))*:y.

Arguments is_test_tensor_map {R n A av} hA {Y NY hNY E ev} hE {T W} mu nu F.
