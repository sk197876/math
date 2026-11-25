(** Federer (1969), 4.1.11, pp. 365–366: a product map
    pulls a separated test back by pulling each factor back.
    Reuse the actual product differential of 3.2.23, the pullback
    laws of 4.1.6–4.1.7 and the preceding block covector identity.
    The original open domains and every mixed degree are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLocal NormOpenDomainLaws NormRegularity
  NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCartesianLinear
  EuclideanCartesianDifferential AlternatingForms AlternatingDual
  AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentSpaces CurrentMapDifferential CurrentCartesianDomain
  CurrentCartesianMapClass CovectorCartesianMap CurrentDegreeTransport
  CurrentCartesianTestProductSealed SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP
  SmoothFormPullbackSealed FormReindexPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_cartesian_factor_open_class]: restrict
    a globally smooth factor to its original open domain,
    supporting Federer 4.1.11, pp. 365–366, by 3.1.11, p. 220.
    This is an alias of the previously proved restriction laws. *)
Definition current_cartesian_factor_open_class
    (R : realType) (m n : nat) (A : set (R_n R m))
    (hA : forall x, A x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A x)
    (f : R_n R m -> R_n R n)
    (hf : norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (fun _ => True) f) :
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f :=
  fun k => @norm_class_open_restriction R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (fun _ => True) A f k (fun _ _ => Logic.I) hA (hf k).

Section CurrentCartesianMapPullback.
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

(** Source for [current_cartesian_map_pullback_values]: the
    original product-map pullback factors on every separated
    compact test and every mixed degree, supporting Federer
    4.1.11, pp. 365–366. Only equal total degrees are identified;
    the factor pullbacks here are actual smooth forms. *)
Theorem current_cartesian_map_pullback_values d k l (e : (k+l)%N=d)
    (alpha : @current_test_space R h2 n C hC k)
    (beta : @current_test_space R h2 v D hD l) z (hz : AB z) :
  vab d (Pull d (ICD d (Tr _ _ e (Pure k l alpha beta)))) z =
    form_reindex e (form_wedge h2 (@scalar_bilinear R)
      (A_m_dual (hom_as_linear p) (va k (PullF k (IC k alpha)) (p z)))
      (A_m_dual (hom_as_linear q) (vb l (PullG l (ID l beta)) (q z)))).
Proof.
pose L := @current_map_differential R m n (fun _ => True) f (p z).
pose M := @current_map_differential R mu v (fun _ => True) g (q z).
have hLFull := @current_map_differential_actual R m n
  (fun _ => True) f hf (p z) Logic.I.
have hMFull := @current_map_differential_actual R mu v
  (fun _ => True) g hg (q z) Logic.I.
have hL := @norm_differential_restrict R X N NX NN
  (fun _ => True) A f (p z) L (fun _ _ => Logic.I)
  (@hA (p z) hz.1) hLFull.
have hM := @norm_differential_restrict R Y V NY NV
  (fun _ => True) B g (q z) M (fun _ _ => Logic.I)
  (@hB (q z) hz.2) hMFull.
have hMapFull := @euclidean_cartesian_differential R m mu n v
  f g z L M hLFull hMFull.
have hMap := @norm_differential_restrict R Z W NZ NW
  (fun _ => True) AB F z (@euclidean_cartesian_linear R m mu n v L M)
  (fun _ _ => Logic.I) (@hAB z hz) hMapFull.
have hPull := @smooth_form_pullback_values R (m+mu)%N (n+v)%N d
  AB CD (ECD d) (EAB d) (vcd d) (vab d) F (Pull d)
  (@SmoothFormPullback.laws R h2 (m+mu)%N (n+v)%N d
    AB CD hAB hCD F Image Smooth)
  (ICD d (Tr _ _ e (Pure k l alpha beta))) z
  (@euclidean_cartesian_linear R m mu n v L M) hz hMap.
have hTest := @current_test_degree_transport_values R h2 (n+v)%N
  CD hCD (k+l)%N d e (Pure k l alpha beta) (F z).
have hPure := (@CartesianTestProduct.laws R h2 n v C D hC hD k l).2
  alpha beta (F z) (Image z hz).
have hFirst : p' (F z)=f (p z) := congr1 fst
  (@euclidean_cartesian_map_coordinates R m mu n v f g z).
have hSecond : q' (F z)=g (q z) := congr1 snd
  (@euclidean_cartesian_map_coordinates R m mu n v f g z).
rewrite hPure hFirst hSecond in hTest.
have hFValues := @smooth_form_pullback_values R m n k A C
  (EC k) (EA k) (vc k) (va k) f (PullF k)
  (@SmoothFormPullback.laws R h2 m n k A C hA hC f hFImage hFA)
  (IC k alpha) (p z) L hz.1 hL.
have hGValues := @smooth_form_pullback_values R mu v l B D
  (ED l) (EB l) (vd l) (vb l) g (PullG l)
  (@SmoothFormPullback.laws R h2 mu v l B D hB hD g hGImage hGB)
  (ID l beta) (q z) M hz.2 hM.
have hResult := eq_trans hPull
  (congr1 (fun a : A_m W R^o d =>
    A_m_dual (hom_as_linear
      (@euclidean_cartesian_linear R m mu n v L M)) a) hTest).
rewrite original_linear_pullback_reindex covector_cartesian_map_product
  -hFValues -hGValues in hResult.
exact: hResult.
Qed.
End CurrentCartesianMapPullback.
