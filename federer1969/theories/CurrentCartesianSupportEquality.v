(** Federer (1969), 4.1.8, p. 360: the exact support
    identity for arbitrary original currents. Both inclusions
    were proved from genuine tests and the original support
    definition, without a measure representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentTestValueLaws CurrentSupportGeometry SmoothCompactSet
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation CurrentCartesianDomain
  CurrentCartesianCompactProjections CurrentCartesianSliceTestSealed CurrentCartesianSliceTestSupport
  CurrentCartesianSliceFieldSupport CurrentCartesianSliceSealed CurrentCartesianProductSealed
  CurrentCartesianProductAction FunctionalSupportUP CurrentCartesianOpenCylinders
  CurrentCartesianProductAnnihilation CurrentCartesianSupportLower CurrentCartesianSupportUpper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSupportEquality.
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
(** Source for [current_cartesian_support]: the support of
    S times T is exactly support S times support T,
    Federer 4.1.8, p. 360, including empty domains,
    zero currents and zero-dimensional coordinate blocks. *)
Theorem current_cartesian_support (S:CA) (T:CB):
  @current_support R h2 (m+n) AB hAB (i+j) (Product S T)=
    @euclidean_cartesian_set R m n
      (@current_support R h2 m A hA i S) (@current_support R h2 n B hB j T).
Proof.
apply:funext=>z;apply:propext;split.
- exact:(@current_cartesian_support_upper R h2 m n i j A B hA hB S T z).
- exact:(@current_cartesian_support_lower R h2 m n i j A B hA hB S T z).
Qed.
End CurrentCartesianSupportEquality.
