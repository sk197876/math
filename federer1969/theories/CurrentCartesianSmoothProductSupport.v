(** Federer (1969), 4.1.8, p. 360: the separated smooth
    forms are actual compact tests on A times B. Their supports
    lie in the product of two original compact support bounds.
    The witness compact set is used only in this existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap AlternatingForms AlternatingDual
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  CurrentCartesianDomain CurrentCartesianCompact CurrentCartesianSmoothProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSmoothProductSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation EA := (fun k=>@current_smooth_space R h2 m A hA k).
Local Notation EB := (fun k=>@current_smooth_space R h2 n B hB k).
Local Notation EC := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation va := (fun k=>@current_smooth_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_smooth_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation ta := (fun k=>@current_test_value R h2 m A hA k).
Local Notation tb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation hEA := (fun k=>@current_smooth_space_laws R h2 m A hA k).
Local Notation hEB := (fun k=>@current_smooth_space_laws R h2 n B hB k).
Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation NC := (fun k=>@current_form_comass R h2 (m+n) k).
Local Notation hNC := (fun k=>@current_form_comass_real_norm R h2 (m+n) k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [current_cartesian_smooth_product_compact_support]:
    the separated forms belong to the original compact test space
    in Federer 4.1.8, p. 360, in the paragraph invoking 4.1.3.
    This supporting result proves compact support from the actual
    pointwise product law; it assumes neither a product-test witness
    nor a compact support conclusion. *)
Theorem current_cartesian_smooth_product_compact_support k l
    (G:DA k->DB l->EC (k+l)):
  @is_current_cartesian_smooth_product R h2 m n A B hA hB k l G->
  forall alpha beta,exists K:smooth_compact_set hNZ AB,
    @smooth_function_support R Z (A_m Z R^o (k+l)) NZ hNZ AB
      (EC (k+l)) (vc (k+l)) (G alpha beta) `<=` smooth_compact_carrier K.
Proof.
move=>[_ hValues] alpha beta.
have [KA hKA]:=smooth_test_support_bound (hEA k) alpha.
have [KB hKB]:=smooth_test_support_bound (hEB l) beta.
have hAOff:=(@smooth_function_compact_support_iff R X (A_m X R^o k) NX
  (@current_form_comass R h2 m k) hNX (@current_form_comass_real_norm R h2 m k)
  A (EA k) (va k) (hEA k) KA (smooth_test_inclusion (hEA k) alpha)).1 hKA.
have hBOff:=(@smooth_function_compact_support_iff R Y (A_m Y R^o l) NY
  (@current_form_comass R h2 n l) hNY (@current_form_comass_real_norm R h2 n l)
  B (EB l) (vb l) (hEB l) KB (smooth_test_inclusion (hEB l) beta)).1 hKB.
pose C:=@euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
have hC:C `<=` AB.
  move=>z hz.
  have [hzA hzB]:=(@current_cartesian_domain_coordinates R m n
    (smooth_compact_carrier KA) (smooth_compact_carrier KB) z).1 hz.
  apply:(@current_cartesian_domain_coordinates R m n A B z).2;split.
  - exact:(smooth_compact_in_domain KA (p z) hzA).
  - exact:(smooth_compact_in_domain KB (q z) hzB).
have hCompact:=@current_cartesian_compact R m n
  (smooth_compact_carrier KA) (smooth_compact_carrier KB)
  (smooth_compact_is_compact KA) (smooth_compact_is_compact KB).
pose K:=@Build_smooth_compact_set R Z NZ hNZ AB C hC hCompact.
exists K.
apply:(@smooth_function_compact_support_iff R Z (A_m Z R^o (k+l)) NZ
  (NC (k+l)) hNZ (hNC (k+l)) AB (EC (k+l)) (vc (k+l)) (hEC (k+l))
  K (G alpha beta)).2=>z hOutside.
have hWedge:=@form_wedge_bilinear R h2 Z R^o
  (fun a b:R^o=>a*b) (@scalar_bilinear R) k l.
case:(pselect (AB z))=>hz;last exact:(smooth_function_evaluation_outside
  (hEC (k+l)) (G alpha beta) hz).
have hValue:=@hValues alpha beta z hz.
case:(pselect (smooth_compact_carrier KA (p z)))=>hFirst.
- have hLast:~smooth_compact_carrier KB (q z).
    move=>hLast;apply:hOutside.
    exact:((@current_cartesian_domain_coordinates R m n
      (smooth_compact_carrier KA) (smooth_compact_carrier KB) z).2 (conj hFirst hLast)).
  have hZero:tb l beta (q z)=0:=@hBOff (q z) hLast.
  have hPullback:A_m_dual (hom_as_linear q) (tb l beta (q z))=0.
    rewrite hZero;exact:linear0.
  rewrite hPullback (bil0r hWedge) in hValue;exact:hValue.
- have hZero:ta k alpha (p z)=0:=@hAOff (p z) hFirst.
  have hPullback:A_m_dual (hom_as_linear p) (ta k alpha (p z))=0.
    rewrite hZero;exact:linear0.
  rewrite hPullback (bil0l hWedge) in hValue;exact:hValue.
Qed.
End CurrentCartesianSmoothProductSupport.
