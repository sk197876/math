(** Federer (1969), 4.1.8, p. 360: the original
    slice has its diagonal value and vanishes in every
    off-diagonal separated degree. All identities concern the
    actual test functions on the original open factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP ExteriorMaps ExteriorHomogeneousProducts AlternatingDual
  AlternatingProduct ScalarCoefficients CurrentVectorFormInterior Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing CurrentSpaces
  CurrentTestValueLaws SmoothTestEvaluation CurrentCartesianDomain CurrentCartesianSliceUP
  CurrentCartesianSliceTestSealed CurrentCartesianSliceSealed
  CurrentCartesianTestProductSealed CurrentCartesianCovectorSlice CurrentDegreeTransport
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSeparatedSlice.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation hEA := (@current_smooth_space_laws R h2 m A hA i).
Local Notation va := (@current_test_value R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation vb := (@current_test_value R h2 n B hB j).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).
(** Source for [current_cartesian_separated_slice_test]: the
    original first-variable test for p#alpha wedge q#beta
    equals alpha multiplied by the beta pairing, supporting
    Federer 4.1.8, p. 360. *)
Theorem current_cartesian_separated_slice_test (b:R_n R n) (hb:B b)
    (eta:exterior_power (R_n R n) j) (alpha:DA i) (beta:DB):
  F b hb eta (Pure i j alpha beta)=pairing eta (vb beta b)*:alpha.
Proof.
apply:(smooth_test_values_extensional hEA)=>a ha.
change (va (F b hb eta (Pure i j alpha beta)) a=va (pairing eta (vb beta b)*:alpha) a).
rewrite (@current_test_scale_value R h2 m i A hA).
have hSlice:=((@CartesianSliceTest.laws R h2 m n A B hA hB i j b hb).2
  eta (Pure i j alpha beta) a ha).
rewrite hSlice.
have hJoin:AB (@euclidean_block_join R m n (a,b)).
  change (A (euclidean_block_split (@euclidean_block_join R m n (a,b))).1 /\
    B (euclidean_block_split (@euclidean_block_join R m n (a,b))).2).
  by rewrite euclidean_block_joinK.
have hPure:=(@CartesianTestProduct.laws R h2 m n A B hA hB i j).2
  alpha beta (@euclidean_block_join R m n (a,b)) hJoin.
have hFirst:@euclidean_first_block_map R m n (@euclidean_block_join R m n (a,b))=a.
  exact:(congr1 fst (@euclidean_block_joinK R m n (a,b))).
have hLast:@euclidean_last_block_map R m n (@euclidean_block_join R m n (a,b))=b.
  exact:(congr1 snd (@euclidean_block_joinK R m n (a,b))).
rewrite hFirst hLast in hPure.
rewrite hPure.
change (A_m_dual (hom_as_linear (@euclidean_first_injection_map R m n))
  (@current_vector_form_interior R (R_n R (m+n)) j i
    (ExteriorMaps.exterior_power_map (hom_as_linear (@euclidean_last_injection_map R m n)) j eta)
    (ExteriorHomogeneousProducts.form_reindex (addnC i j)
      (AlternatingProduct.form_wedge h2 (ScalarCoefficients.scalar_bilinear R)
        (A_m_dual (hom_as_linear (@euclidean_first_block_map R m n)) (va alpha a))
        (A_m_dual (hom_as_linear (@euclidean_last_block_map R m n)) (vb beta b)))))=
  pairing eta (vb beta b)*:va alpha a).
exact:(@current_cartesian_covector_slice_diagonal R h2 m n i j (va alpha a) (vb beta b) eta).
Qed.

(** Source for [current_cartesian_separated_slice]: the original
    phi_S of a diagonal separated test equals S(alpha) beta,
    supporting Federer 4.1.8, p. 360. Both original
    degrees may be zero. *)
Theorem current_cartesian_separated_slice (S:CA) (alpha:DA i) (beta:DB):
  H S (Pure i j alpha beta)=@current_value R h2 m A hA i S alpha*:beta.
Proof.
apply:(smooth_test_values_extensional hEB)=>b hb;apply:pairing_ext=>eta.
change (pairing eta (vb (H S (Pure i j alpha beta)) b)=
  pairing eta (vb (@current_value R h2 m A hA i S alpha*:beta) b)).
rewrite (@current_test_scale_value R h2 n j B hB)
  (bilZr (@pairing_bilinear R (R_n R n) R^o j)).
rewrite (@CartesianSlice.laws R h2 m n i j A B hA hB S (Pure i j alpha beta) b hb eta)
  current_cartesian_separated_slice_test linearZ.
exact:mulrC.
Qed.

(** Source for [current_cartesian_separated_slice_test_off_diagonal]:
    the first-variable original slice test is zero in every
    other mixed degree, supporting Federer 4.1.8, p. 360.
    The degree transport identifies only the equal totals. *)
Theorem current_cartesian_separated_slice_test_off_diagonal k l (e:(k+l)%N=(i+j)%N)
    (b:R_n R n) (hb:B b) (eta:exterior_power (R_n R n) j)
    (alpha:DA k) (beta:@current_test_space R h2 n B hB l):
  k<>i->F b hb eta (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e
    (Pure k l alpha beta))=0.
Proof.
move=>hDifferent;apply:(smooth_test_values_extensional hEA)=>a ha.
change (va (F b hb eta (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e
  (Pure k l alpha beta))) a=va 0 a).
rewrite (@current_test_zero_value R h2 m i A hA).
have hSlice:=((@CartesianSliceTest.laws R h2 m n A B hA hB i j b hb).2
  eta (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e
    (Pure k l alpha beta)) a ha).
rewrite hSlice current_test_degree_transport_values.
have hJoin:AB (@euclidean_block_join R m n (a,b)).
  change (A (euclidean_block_split (@euclidean_block_join R m n (a,b))).1 /\
    B (euclidean_block_split (@euclidean_block_join R m n (a,b))).2).
  by rewrite euclidean_block_joinK.
have hPure:=(@CartesianTestProduct.laws R h2 m n A B hA hB k l).2
  alpha beta (@euclidean_block_join R m n (a,b)) hJoin.
have hFirst:@euclidean_first_block_map R m n (@euclidean_block_join R m n (a,b))=a.
  exact:(congr1 fst (@euclidean_block_joinK R m n (a,b))).
have hLast:@euclidean_last_block_map R m n (@euclidean_block_join R m n (a,b))=b.
  exact:(congr1 snd (@euclidean_block_joinK R m n (a,b))).
rewrite hFirst hLast in hPure.
rewrite hPure.
exact:(@current_cartesian_covector_slice_off_diagonal R h2 m n i j k l e
  (@current_test_value R h2 m A hA k alpha a)
  (@current_test_value R h2 n B hB l beta b) eta hDifferent).
Qed.

(** Source for [current_cartesian_separated_slice_off_diagonal]:
    the original phi_S is zero for every off-diagonal
    separated test, supporting Federer 4.1.8, p. 360.
    The assertion holds for arbitrary original currents S. *)
Theorem current_cartesian_separated_slice_off_diagonal (S:CA) k l (e:(k+l)%N=(i+j)%N)
    (alpha:DA k) (beta:@current_test_space R h2 n B hB l):
  k<>i->H S (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e
    (Pure k l alpha beta))=0.
Proof.
move=>hDifferent;apply:(smooth_test_values_extensional hEB)=>b hb;apply:pairing_ext=>eta.
change (pairing eta (vb (H S (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e
  (Pure k l alpha beta))) b)=pairing eta (vb 0 b)).
rewrite (@CartesianSlice.laws R h2 m n i j A B hA hB S _ b hb eta)
  (@current_cartesian_separated_slice_test_off_diagonal k l e b hb eta alpha beta hDifferent)
  linear0 (@current_test_zero_value R h2 n j B hB)
  (bil0r (@pairing_bilinear R (R_n R n) R^o j)).
reflexivity.
Qed.
End CurrentCartesianSeparatedSlice.
