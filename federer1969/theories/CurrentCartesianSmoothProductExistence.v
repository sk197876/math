(** Federer (1969), 4.1.8, p. 360: the separated form exists
    in the actual smooth space. Construct a witness only inside
    this existence proof, using the public smooth pullbacks and
    smooth alternating product. Compact support is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear BilinearPrecompose RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients
  CurrentSpaces SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP
  SmoothFormPullbackSealed SmoothCurrentFormProduct SmoothCurrentFormProductBilinear
  CurrentCartesianDomain CurrentCartesianProjections CurrentCartesianSmoothProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSmoothProductExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
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
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [current_cartesian_smooth_product_exists]: the
    actual smooth form p#alpha wedge q#beta used in Federer
    4.1.8, p. 360 exists for every pair of original tests.
    Bilinearity uses the preceding smooth-product law and the
    earlier composition of bilinear and linear maps. *)
Theorem current_cartesian_smooth_product_exists k l:
  exists G:DA k->DB l->EC (k+l),
    @is_current_cartesian_smooth_product R h2 m n A B hA hB k l G.
Proof.
pose hImageP:=fun z (hz:AB z)=>hz.1.
pose hImageQ:=fun z (hz:AB z)=>hz.2.
pose hPSmooth:=@current_cartesian_first_projection_smooth R m n A B hA hB.
pose hQSmooth:=@current_cartesian_last_projection_smooth R m n A B hA hB.
pose IA:=smooth_test_inclusion (hEA k).
pose IB:=smooth_test_inclusion (hEB l).
pose PA:=@SmoothFormPullback.operator R h2 (m+n) m k AB A hAB hA
  p hImageP hPSmooth.
pose PB:=@SmoothFormPullback.operator R h2 (m+n) n l AB B hAB hB
  q hImageQ hQSmooth.
pose G (alpha:DA k) (beta:DB l):=
  @smooth_current_form_product R h2 (m+n) k l AB hAB (PA (IA alpha)) (PB (IB beta)).
have hPA:=@SmoothFormPullback.laws R h2 (m+n) m k AB A hAB hA
  p hImageP hPSmooth.
have hPB:=@SmoothFormPullback.laws R h2 (m+n) n l AB B hAB hB
  q hImageQ hQSmooth.
have hPoint alpha beta z (hz:AB z):
    vc (k+l) (G alpha beta) z=
    @form_wedge R h2 Z R^o (fun a b:R^o=>a*b) (@scalar_bilinear R) k l
      (A_m_dual (hom_as_linear p) (ta k alpha (p z)))
      (A_m_dual (hom_as_linear q) (tb l beta (q z))).
  have hFirst:=@smooth_form_pullback_values R (m+n) m k AB A
    (EA k) (EC k) (va k) (vc k) p PA hPA (IA alpha) z p hz
    (@current_cartesian_first_projection_differential R m n A B hA hB z hz).
  have hLast:=@smooth_form_pullback_values R (m+n) n l AB B
    (EB l) (EC l) (vb l) (vc l) q PB hPB (IB beta) z q hz
    (@current_cartesian_last_projection_differential R m n A B hA hB z hz).
  have hProduct:=@smooth_current_form_product_values R h2 (m+n) k l AB hAB
    (PA (IA alpha)) (PB (IB beta)) z hz.
  exact:(eq_trans hProduct (congr2
    (@form_wedge R h2 Z R^o (fun a b:R^o=>a*b) (@scalar_bilinear R) k l)
    hFirst hLast)).
have hBilinear:=@bilinear_linear_precompose R (DA k) (DB l) (EC k) (EC l) (EC (k+l))
  (fun phi psi=>@smooth_current_form_product R h2 (m+n) k l AB hAB phi psi)
  (@smooth_current_form_product_bilinear R h2 (m+n) k l AB hAB)
  (hom_as_linear (hom_comp PA IA)) (hom_as_linear (hom_comp PB IB)).
exists G;split;[exact:hBilinear|exact:hPoint].
Qed.
End CurrentCartesianSmoothProductExistence.
