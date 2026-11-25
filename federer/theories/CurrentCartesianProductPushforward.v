(** Federer (1969), 4.1.11, pp. 365–366: proper
    pushforward commutes with the original Cartesian current product
    for the globally smooth maps used here. The proof reuses every
    mixed test degree, the existing compact cutoff operator and
    the original product-density theorem. No mass bound is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianMapClass
  CurrentCartesianMapPullback CurrentCartesianMapReplacement
  CurrentCartesianProductSealed CurrentCartesianCompactCurrents
  CurrentCartesianMixedExtensional CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentCartesianTestProductSealed
  CurrentProperSupport CurrentCompactMapProper CurrentProperPullbackTests
  CurrentPushforwardUP CurrentPushforwardSealed SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentCartesianProductPushforward.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables m mu n v : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R mu).
Local Notation Z := (R_n R (m+mu)%N).
Local Notation N := (R_n R n).
Local Notation V := (R_n R v).
Local Notation W := (R_n R (n+v)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R mu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+mu)%N)).
Local Notation NN := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NV := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R (n+v)%N)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY :=
  (inner_norm_real_norm (@euclidean_inner_productP R mu)).
Local Notation hNZ :=
  (inner_norm_real_norm (@euclidean_inner_productP R (m+mu)%N)).
Local Notation hNN :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNV :=
  (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNW :=
  (inner_norm_real_norm (@euclidean_inner_productP R (n+v)%N)).
Variables (A : set X) (B : set Y) (C : set N) (D : set V).
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.
Hypothesis hB : forall y, B y -> norm_domain_interior NY B y.
Hypothesis hC : forall x, C x -> norm_domain_interior NN C x.
Hypothesis hD : forall y, D y -> norm_domain_interior NV D y.
Local Notation AB := (@euclidean_cartesian_set R m mu A B).
Local Notation CD := (@euclidean_cartesian_set R n v C D).
Local Notation hAB := (@current_cartesian_domain_open R m mu A B hA hB).
Local Notation hCD := (@current_cartesian_domain_open R n v C D hC hD).
Variables (f : X -> N) (g : Y -> V).
Hypothesis hf : norm_class_all_orders hNX hNN (fun _ => True) f.
Hypothesis hg : norm_class_all_orders hNY hNV (fun _ => True) g.
Hypothesis hFImage : forall x, A x -> C (f x).
Hypothesis hGImage : forall y, B y -> D (g y).
Local Notation F := (@euclidean_cartesian_map R m mu n v f g).
Local Notation p := (@euclidean_first_block_map R m mu).
Local Notation q := (@euclidean_last_block_map R m mu).
Local Notation p' := (@euclidean_first_block_map R n v).
Local Notation q' := (@euclidean_last_block_map R n v).
Local Notation hFA := (@current_cartesian_factor_open_class
  R m n A hA f hf).
Local Notation hGB := (@current_cartesian_factor_open_class
  R mu v B hB g hg).
Local Notation Image := (fun z hz =>
  @current_cartesian_map_domain_image R m mu n v A B C D f g
    hFImage hGImage z hz).
Local Notation Smooth :=
  (@current_cartesian_map_on_open_product_smooth R m mu n v
    f g hf hg A B hA hB).
Local Notation EA := (fun k => @current_smooth_space R h2 m A hA k).
Local Notation EB := (fun k => @current_smooth_space R h2 mu B hB k).
Local Notation EC := (fun k => @current_smooth_space R h2 n C hC k).
Local Notation ED := (fun k => @current_smooth_space R h2 v D hD k).
Local Notation EAB :=
  (fun k => @current_smooth_space R h2 (m+mu)%N AB hAB k).
Local Notation ECD :=
  (fun k => @current_smooth_space R h2 (n+v)%N CD hCD k).
Local Notation va := (fun k => @current_smooth_value R h2 m A hA k).
Local Notation vb := (fun k => @current_smooth_value R h2 mu B hB k).
Local Notation vc := (fun k => @current_smooth_value R h2 n C hC k).
Local Notation vd := (fun k => @current_smooth_value R h2 v D hD k).
Local Notation vab :=
  (fun k => @current_smooth_value R h2 (m+mu)%N AB hAB k).
Local Notation vcd :=
  (fun k => @current_smooth_value R h2 (n+v)%N CD hCD k).
Local Notation IC := (fun k => smooth_test_inclusion
  (@current_smooth_space_laws R h2 n C hC k)).
Local Notation ID := (fun k => smooth_test_inclusion
  (@current_smooth_space_laws R h2 v D hD k)).
Local Notation ICD := (fun k => smooth_test_inclusion
  (@current_smooth_space_laws R h2 (n+v)%N CD hCD k)).
Local Notation Pure := (fun k l =>
  @CartesianTestProduct.value R h2 n v C D hC hD k l).
Local Notation Tr := (fun a b (e : a=b) =>
  @current_test_degree_transport R h2 (n+v)%N CD hCD a b e).
Local Notation PullF := (fun k =>
  @SmoothFormPullback.operator R h2 m n k A C hA hC
    f hFImage hFA).
Local Notation PullG := (fun k =>
  @SmoothFormPullback.operator R h2 mu v k B D hB hD
    g hGImage hGB).
Local Notation Pull := (fun k =>
  @SmoothFormPullback.operator R h2 (m+mu)%N (n+v)%N k
    AB CD hAB hCD F Image Smooth).

Variables i j : nat.
Variable S : @current_space R h2 m A hA i.
Variable T : @current_space R h2 mu B hB j.
Hypothesis hS : @compact (real_norm_metric_space hNX)
  (@current_support R h2 m A hA i S).
Hypothesis hT : @compact (real_norm_metric_space hNY)
  (@current_support R h2 mu B hB j T).
Local Notation Product :=
  (@CartesianCurrentProduct.value R h2 m mu i j A B hA hB S T).
Local Notation ProperF := (@current_compact_map_proper R h2 m n i
  A C hA S f hFImage (norm_class_continuous (hFA 0%N)) hS).
Local Notation ProperG := (@current_compact_map_proper R h2 mu v j
  B D hB T g hGImage (norm_class_continuous (hGB 0%N)) hT).
Local Notation Proper := (@current_compact_map_proper R h2
  (m+mu)%N (n+v)%N (i+j)%N AB CD hAB Product F Image
  (norm_class_continuous (Smooth 0%N))
  (@current_cartesian_compact_currents R h2 m mu i j A B hA hB S T hS hT)).
Local Notation PushF :=
  (@CurrentPushforward.value R h2 m n i A C hA hC S f hFImage hFA ProperF).
Local Notation PushG :=
  (@CurrentPushforward.value R h2 mu v j B D hB hD T g hGImage hGB ProperG).
Local Notation Left :=
  (@CurrentPushforward.value R h2 (m+mu)%N (n+v)%N (i+j)%N
    AB CD hAB hCD Product F Image Smooth Proper).
Local Notation Right :=
  (@CartesianCurrentProduct.value R h2 n v i j C D hC hD PushF PushG).
Local Notation SourcePure := (fun k l =>
  @CartesianTestProduct.value R h2 m mu A B hA hB k l).
Local Notation SourceTr := (fun a b (e : a=b) =>
  @current_test_degree_transport R h2 (m+mu)%N AB hAB a b e).

(** Source for [current_cartesian_product_pushforward]: the
    original product pushforward equals f#S times g#T, supporting
    the slice, affine-map and associativity identities in Federer
    4.1.11, pp. 365–366. Both currents are arbitrary and compactly
    supported. Global smoothness is the proved condition of the
    polynomial maps used here; it is not added to the join inputs. *)
Theorem current_cartesian_product_pushforward : Left = Right.
Proof.
apply: (@current_cartesian_mixed_values_extensional R h2 n v C D hC hD (i+j)%N).
move=> k l e alpha beta.
have [KC hKC] := smooth_test_support_bound
  (@current_smooth_space_laws R h2 n C hC k) alpha.
have [KD hKD] := smooth_test_support_bound
  (@current_smooth_space_laws R h2 v D hD l) beta.
have [FirstQ [hFirstContinuous [O [hO [hSO [hOA hFirstAgreement]]]]]] :=
  @current_proper_pullback_tests R h2 m n k i A C hA hC
    S f hFImage hFA ProperF KC.
have [SecondQ [hSecondContinuous [Q [hQ [hTQ [hQB hSecondAgreement]]]]]] :=
  @current_proper_pullback_tests R h2 mu v l j B D hB hD
    T g hGImage hGB ProperG KD.
pose chi := FirstQ (IC k alpha).
pose psi := SecondQ (ID l beta).
have hChi x (hx : O x) : @current_test_value R h2 m A hA k chi x =
    va k (PullF k (IC k alpha)) x.
  exact: hFirstAgreement (IC k alpha) hKC x hx.
have hPsi y (hy : Q y) : @current_test_value R h2 mu B hB l psi y =
    vb l (PullG l (ID l beta)) y.
  exact: hSecondAgreement (ID l beta) hKD y hy.
have hReplacement := @current_cartesian_map_product_replacement R h2
  m mu n v A B C D hA hB hC hD f g hf hg hFImage hGImage
  i j k l e S T alpha beta chi psi O Q hO hQ hSO hTQ hOA hQB hChi hPsi.
have hLeft := @CurrentPushforward.laws R h2 (m+mu)%N (n+v)%N
  (i+j)%N AB CD hAB hCD Product F Image Smooth Proper
  (Tr _ _ e (Pure k l alpha beta))
  (SourceTr _ _ e (SourcePure k l chi psi)) hReplacement.
case: (pselect (k = i)) => hDegree.
- subst k.
  have hOther : l = j.
    apply/eqP; have hEq : (i+l == i+j)%N := introT eqP e.
    by rewrite eqn_add2l in hEq.
  subst l.
  have hFirstReplacement : @is_current_pullback_test_replacement R h2
      m n i A C hA hC S f hFImage hFA alpha chi.
    exists O; split; first exact: hO.
    split; first exact: hSO.
    split; first exact: hOA.
    exact: hChi.
  have hSecondReplacement : @is_current_pullback_test_replacement R h2
      mu v j B D hB hD T g hGImage hGB beta psi.
    exists Q; split; first exact: hQ.
    split; first exact: hTQ.
    split; first exact: hQB.
    exact: hPsi.
  have hFValue := @CurrentPushforward.laws R h2 m n i A C hA hC
    S f hFImage hFA ProperF alpha chi hFirstReplacement.
  have hGValue := @CurrentPushforward.laws R h2 mu v j B D hB hD
    T g hGImage hGB ProperG beta psi hSecondReplacement.
  rewrite !current_test_degree_transport_identity in hLeft.
  by rewrite !current_test_degree_transport_identity hLeft
    ((@CartesianCurrentProduct.laws R h2 m mu i j A B hA hB S T).1 chi psi)
    ((@CartesianCurrentProduct.laws R h2 n v i j C D hC hD PushF PushG).1 alpha beta)
    hFValue hGValue.
- have hSourceZero := (@CartesianCurrentProduct.laws R h2 m mu i j
    A B hA hB S T).2 k l e hDegree chi psi.
  have hTargetZero := (@CartesianCurrentProduct.laws R h2 n v i j
    C D hC hD PushF PushG).2 k l e hDegree alpha beta.
  by rewrite hLeft hSourceZero hTargetZero.
Qed.
End CurrentCartesianProductPushforward.
