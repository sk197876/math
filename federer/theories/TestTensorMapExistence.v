(** Federer (1969), 4.1.3, p. 348: the actual canonical
    tensor map exists. Smooth compact products give its pure
    values, and the original two tensor universal properties
    extend them. No tensor construction or extra topology
    premise enters the independent specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP TensorFamilyUP FamilyUpdate RealNormUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  TestPointwiseLinearLaws TestCoordinateProductRepresentation TestCoordinateProductUpdate
  TestTensorMapUP SeparatedTestTensorLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TestTensorMapExistence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Local Notation D1 := (smooth_test_space hA).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Dn := (smooth_test_space hE).
Variable T W:lmodType R.
Variable mu:{dffun forall i:'I_n,D1}->T.
Variable nu:T->Y->W.
Hypothesis hT:is_tensor_product_family mu.
Hypothesis hW:is_tensor_product nu.

(** Source for [test_tensor_map_exists]: the canonical map
    whose image is discussed in Federer 4.1.3, p. 348.
    Its pure-tensor evaluation formula is proved from actual
    compactly supported products. *)
Theorem test_tensor_map_exists:
  exists F:Hom W Dn,is_test_tensor_map hA hE mu nu F.
Proof.
have hFor f:exists b:Y->Dn,forall y x,
    smooth_test_value hE (b y) x=(\prod_i smooth_test_value hA (f i) (x i))*:y.
  have[b hb]:=choice (@test_coordinate_vector_product_exists R n A av hA Y NY hNY E ev hE f).
  by exists b.
have[beta hBeta]:=choice hFor.
have hFirst y:multilinear (fun f=>beta f y).
  move=>f i c v w.
  apply:(smooth_test_values_extensional hE)=>x _.
  rewrite test_value_linear_combination !hBeta !test_coordinate_product_update
    test_value_linear_combination.
  by rewrite mulrDl scalerDl !scalerA mulrA.
have hSecond f:linear (beta f).
  move=>c y z.
  apply:(smooth_test_values_extensional hE)=>x _.
  rewrite test_value_linear_combination !hBeta.
  by rewrite scalerDr !scalerA mulrC.
have[F hF]:=@separated_test_tensor_lift_exists R n (fun _=>D1)
  T Y W Dn mu nu hT hW beta hFirst hSecond.
exists (hom_of_linear F)=>f y x.
rewrite hom_of_linearE hF; exact:(hBeta f y x).
Qed.
End TestTensorMapExistence.
