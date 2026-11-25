(** Federer (1969), 4.1.3, p. 348: the canonical tensor
    map is opaque and determined only by its original pure
    test evaluation law. Its algebraic existence was proved
    without completeness or target separability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP TensorFamilyUP RealNormUP GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SmoothFunctionSpaceUP SmoothTestSpaces
  TestTensorMapUP TestTensorMapExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type TestTensorMapSignature.
(** Source for [value]: the original canonical map to D(R^n,Y),
    Federer 4.1.3, p. 348. *)
Parameter value:forall (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av)
  (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
  (E:lmodType R) (ev:E->R_n R n->Y)
  (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
    hNY (fun _=>True) ev) (T W:lmodType R)
  (mu:{dffun forall i:'I_n,smooth_test_space hA}->T) (nu:T->Y->W)
  (hT:is_tensor_product_family mu) (hW:is_tensor_product nu),Hom W (smooth_test_space hE).
(** Source for [laws]: the actual pure coordinate-product values
    characterize the canonical tensor map, Federer 4.1.3, p. 348. *)
Parameter laws:forall (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av)
  (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
  (E:lmodType R) (ev:E->R_n R n->Y)
  (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
    hNY (fun _=>True) ev) (T W:lmodType R)
  (mu:{dffun forall i:'I_n,smooth_test_space hA}->T) (nu:T->Y->W)
  (hT:is_tensor_product_family mu) (hW:is_tensor_product nu),is_test_tensor_map hA hE mu nu
  (@value R n A av hA Y NY hNY E ev hE T W mu nu hT hW).
End TestTensorMapSignature.
Module TestTensorMap:TestTensorMapSignature.
(** Source for [value]: private choice from the proved tensor
    map existence, hidden for Federer 4.1.3, p. 348. *)
Definition value (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av)
  (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
  (E:lmodType R) (ev:E->R_n R n->Y)
  (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
    hNY (fun _=>True) ev) (T W:lmodType R)
  (mu:{dffun forall i:'I_n,smooth_test_space hA}->T) (nu:T->Y->W)
  (hT:is_tensor_product_family mu) (hW:is_tensor_product nu):Hom W (smooth_test_space hE):=
  projT1 (cid (@test_tensor_map_exists R n A av hA Y NY hNY E ev hE T W mu nu hT hW)).
(** Source for [laws]: retain only the independently specified
    original value laws, Federer 4.1.3, p. 348. *)
Lemma laws (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av)
  (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
  (E:lmodType R) (ev:E->R_n R n->Y)
  (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
    hNY (fun _=>True) ev) (T W:lmodType R)
  (mu:{dffun forall i:'I_n,smooth_test_space hA}->T) (nu:T->Y->W)
  (hT:is_tensor_product_family mu) (hW:is_tensor_product nu):is_test_tensor_map hA hE mu nu (@value R n A av hA Y NY hNY E ev hE T W mu nu hT hW).
Proof. exact:(projT2 (cid (@test_tensor_map_exists R n A av hA Y NY hNY E ev hE T W mu nu hT hW))). Qed.
End TestTensorMap.
