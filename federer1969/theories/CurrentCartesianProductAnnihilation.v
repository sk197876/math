(** Federer (1969), 4.1.8, p. 360: on
    the product support is contained in the product of
    the factor supports. These supporting all-test annihilation
    laws use the actual slice and exact compact support
    of each test, without a measure representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentTestValueLaws CurrentSupportGeometry SmoothCompactSet
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation CurrentCartesianDomain
  CurrentCartesianCompactProjections CurrentCartesianSliceTestSealed CurrentCartesianSliceTestSupport
  CurrentCartesianSliceFieldSupport CurrentCartesianSliceSealed CurrentCartesianProductSealed
  CurrentCartesianProductAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianProductAnnihilation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation hDC := (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation hDB := (@current_smooth_derivative_laws R h2 n B hB j).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).

Local Notation Product := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation CB := (@current_space R h2 n B hB j).
Local Notation DA := (@current_test_space R h2 m A hA i).
Local Notation ea := (@current_value R h2 m A hA i).
Local Notation eb := (@current_value R h2 n B hB j).
Local Notation ec := (@current_value R h2 (m+n) AB hAB (i+j)).
Local Notation supportA := (@current_test_support R h2 m i A hA).
Local Notation supportB := (@current_test_support R h2 n j B hB).
Local Notation supportC := (@current_test_support R h2 (m+n) (i+j) AB hAB).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation F := (fun (b:Y) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).
(** Source for [current_cartesian_product_first_annihilation]:
    the product annihilates every original test whose first
    projected support lies in an annihilation region of S,
    supporting the exact support identity of Federer 4.1.8,
    p. 360. The argument uses the actual slice and
    its exact compact projection, without a measure representation. *)
Theorem current_cartesian_product_first_annihilation (S:CA) (T:CB) (W:set X):
  (forall a:DA,supportA a `<=` W->ea S a=0)->
  forall phi:DC,supportC phi `<=` [set z|W (p z)]->ec (Product S T) phi=0.
Proof.
move=>hAnn phi hSupport.
pose K:=@Build_smooth_compact_set R Z NZ hNZ AB (supportC phi)
  (fun z hz=>hz.1) (smooth_test_support_compact hEC phi).
have hExact:@smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
    (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K.
  by move=>z hz.
have[KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
have hOutput:H S phi=0.
  apply:(smooth_test_values_extensional hEB)=>b hb;apply:pairing_ext=>eta.
  change (pairing eta (@current_test_value R h2 n B hB j (H S phi) b)=
    pairing eta (@current_test_value R h2 n B hB j 0 b)).
  rewrite (@CartesianSlice.laws R h2 m n i j A B hA hB S phi b hb eta)
    (@current_test_zero_value R h2 n j B hB) (bil0r (@pairing_bilinear R Y R^o j)).
  apply:hAnn=>a ha.
  have hBound:=@current_cartesian_slice_test_fixed_support R h2 m n i j A B hA hB
    K KA hKA phi hExact b hb eta.
  have hIn:=hBound a ha.
  rewrite hKA in hIn.
  have[z hz he]:=hIn.
  rewrite -he;exact:(hSupport z hz).
by rewrite current_cartesian_product_action hOutput linear0.
Qed.

(** Source for [current_cartesian_product_second_annihilation]:
    the product annihilates every original test whose second
    projected support lies in an annihilation region of T,
    supporting the exact support identity of Federer 4.1.8,
    p. 360. The output slice has precisely the required
    second-projection support bound for every original current S. *)
Theorem current_cartesian_product_second_annihilation (S:CA) (T:CB) (W:set Y):
  (forall b:DB,supportB b `<=` W->eb T b=0)->
  forall phi:DC,supportC phi `<=` [set z|W (q z)]->ec (Product S T) phi=0.
Proof.
move=>hAnn phi hSupport.
pose K:=@Build_smooth_compact_set R Z NZ hNZ AB (supportC phi)
  (fun z hz=>hz.1) (smooth_test_support_compact hEC phi).
have hExact:@smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
    (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K.
  by move=>z hz.
have[KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
have hBound:=@current_cartesian_slice_field_fixed_support R h2 m n i j A B hA hB S K KB phi
  (smooth_test_inclusion hEB (H S phi)) hKB hExact
  (@CartesianSlice.laws R h2 m n i j A B hA hB S phi).
rewrite current_cartesian_product_action.
apply:hAnn=>b hb.
have hIn:=hBound b hb.
rewrite hKB in hIn.
have[z hz he]:=hIn.
rewrite -he;exact:(hSupport z hz).
Qed.
End CurrentCartesianProductAnnihilation.
