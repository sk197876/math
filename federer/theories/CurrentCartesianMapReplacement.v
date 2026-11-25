(** Federer (1969), 4.1.11, pp. 365–366: separated
    compact pullback replacements compute the original product-map
    pushforward. Reuse the actual mixed-degree pullback identity,
    original Cartesian support and the preceding open cylinders. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormOpenTopology NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianMapClass
  CurrentCartesianMapPullback CurrentCartesianProductSealed
  CurrentCartesianSupportUpper CurrentCartesianOpenCylinders
  CurrentDegreeTransport CurrentCartesianTestProductSealed
  CurrentPushforwardUP SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentCartesianMapReplacement.
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

Local Notation SourcePure := (fun k l =>
  @CartesianTestProduct.value R h2 m mu A B hA hB k l).
Local Notation SourceTr := (fun a b (e : a=b) =>
  @current_test_degree_transport R h2 (m+mu)%N AB hAB a b e).

(** Source for [current_cartesian_map_product_replacement]:
    original factor replacements near spt S and spt T give a
    genuine product replacement near spt(S times T), supporting
    the product-map identities in Federer 4.1.11, pp. 365–366.
    The form degrees may differ from both current degrees. *)
Theorem current_cartesian_map_product_replacement i j k l
    (e : (k+l)%N=(i+j)%N)
    (S : @current_space R h2 m A hA i)
    (T : @current_space R h2 mu B hB j)
    (alpha : @current_test_space R h2 n C hC k)
    (beta : @current_test_space R h2 v D hD l)
    (chi : @current_test_space R h2 m A hA k)
    (psi : @current_test_space R h2 mu B hB l)
    (O : set X) (Q : set Y)
    (hO : @open (real_norm_metric_space hNX) O)
    (hQ : @open (real_norm_metric_space hNY) Q)
    (hSO : forall x, @current_support R h2 m A hA i S x -> O x)
    (hTQ : forall y, @current_support R h2 mu B hB j T y -> Q y)
    (hOA : forall x, O x -> A x)
    (hQB : forall y, Q y -> B y)
    (hChi : forall x, O x ->
      @current_test_value R h2 m A hA k chi x =
        va k (PullF k (IC k alpha)) x)
    (hPsi : forall y, Q y ->
      @current_test_value R h2 mu B hB l psi y =
        vb l (PullG l (ID l beta)) y) :
  @is_current_pullback_test_replacement R h2 (m+mu)%N (n+v)%N
    (i+j)%N AB CD hAB hCD
    (@CartesianCurrentProduct.value R h2 m mu i j A B hA hB S T)
    F Image Smooth (Tr _ _ e (Pure k l alpha beta))
    (SourceTr _ _ e (SourcePure k l chi psi)).
Proof.
pose E := (AB `&` [set z | O (p z)]) `&`
  (AB `&` [set z | Q (q z)]).
exists E; split.
- exact: openI
    (@current_cartesian_first_cylinder_open R m mu A B hA hB O hO)
    (@current_cartesian_second_cylinder_open R m mu A B hA hB Q hQ).
- split.
  + move=> z hz.
    have hDomain : AB z := hz.1.
    have hFactors := @current_cartesian_support_upper R h2 m mu i j
      A B hA hB S T z hz.
    exact: conj (conj hDomain (hSO _ hFactors.1))
      (conj hDomain (hTQ _ hFactors.2)).
  + split; first by move=> z hz; exact: hz.1.1.
    move=> z hz.
    have hTest := @current_test_degree_transport_values R h2 (m+mu)%N
      AB hAB (k+l)%N (i+j)%N e (SourcePure k l chi psi) z.
    have hPure := (@CartesianTestProduct.laws R h2 m mu A B hA hB k l).2
      chi psi z hz.1.1.
    rewrite hPure (hChi _ hz.1.2) (hPsi _ hz.2.2) in hTest.
    exact: (eq_trans hTest
      (esym (@current_cartesian_map_pullback_values R h2 m mu n v
        A B C D hA hB hC hD f g hf hg hFImage hGImage
        (i+j)%N k l e alpha beta z hz.1.1))).
Qed.
End CurrentCartesianMapReplacement.
