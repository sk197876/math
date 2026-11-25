(** Federer (1969), 4.1.11, p. 365, the four boundary formulas:
    the first projection of a compact product is evaluated by
    a second-factor scalar cutoff. Reuse the original separated
    test laws and the degree-zero right unit of 1.4.2, p. 18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear BilinearPrecompose RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients
  CurrentSpaces SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP
  SmoothFormPullbackSealed SmoothCurrentFormProduct SmoothCurrentFormProductBilinear
  CurrentCartesianDomain CurrentCartesianProjections CurrentCartesianSmoothProductUP CurrentCartesianTestProductSealed SmoothFunctionSpaceLaws CurrentDegreeTransport
  Alternating AlternatingZero AlternatingSum ExteriorHomogeneousProducts AlternatingUnit ZeroFormScalarProduct ComassWedgeSymmetry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianFirstCutoffValues.
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
Local Notation tc := (fun k=>@current_test_value R h2 (m+n) AB hAB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation ta := (fun k=>@current_test_value R h2 m A hA k).
Local Notation tb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation hEA := (fun k=>@current_smooth_space_laws R h2 m A hA k).
Local Notation hEB := (fun k=>@current_smooth_space_laws R h2 n B hB k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation IA := (fun k=>smooth_test_inclusion (hEA k)).
Local Notation IB := (fun k=>smooth_test_inclusion (hEB k)).
Local Notation IC := (fun k=>smooth_test_inclusion (hEC k)).
Local Notation ImageP := (fun z (hz:AB z)=>hz.1).
Local Notation ImageQ := (fun z (hz:AB z)=>hz.2).
Local Notation PSmooth := (@current_cartesian_first_projection_smooth R m n A B hA hB).
Local Notation QSmooth := (@current_cartesian_last_projection_smooth R m n A B hA hB).
Local Notation PA := (fun k=>@SmoothFormPullback.operator R h2 (m+n) m k AB A hAB hA p ImageP PSmooth).
Local Notation PB := (fun k=>@SmoothFormPullback.operator R h2 (m+n) n k AB B hAB hB q ImageQ QSmooth).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).

Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).

(** Source for [current_cartesian_first_cutoff_values]: a
    second-factor scalar cutoff equal to one gives the actual
    first-projection pullback. This is a supporting identity for
    the endpoint terms of Federer 4.1.11, p. 365. *)
Theorem current_cartesian_first_cutoff_values d (alpha:DA d) (gamma:DB 0%N) z:
  AB z->@current_test_value R h2 n B hB 0%N gamma (q z)=@zero_form R Y R^o 1->
  @current_test_value R h2 (m+n) AB hAB d
    (Tr _ _ (addn0 d) (Pure d 0 alpha gamma)) z=
    vc d (PA d (IA d alpha)) z.
Proof.
move=>hz hGamma.
have hTest:=@current_test_degree_transport_values R h2 (m+n) AB hAB (d+0) d (addn0 d)
  (Pure d 0 alpha gamma) z.
have hPure:=(@CartesianTestProduct.laws R h2 m n A B hA hB d 0%N).2 alpha gamma z hz.
rewrite hPure hGamma in hTest.
have hScalar:A_m_dual (hom_as_linear q) (@zero_form R Y R^o 1)=@zero_form R Z R^o 1.
  apply:form_ext=>t;by rewrite A_m_dualE !zero_formE.
rewrite hScalar in hTest.
have hUnit:form_reindex (addn0 d)
    (form_wedge h2 (scalar_bilinear R)
      (A_m_dual (hom_as_linear p) (ta d alpha (p z)))
      (@zero_form R Z R^o 1)) =
    A_m_dual (hom_as_linear p) (ta d alpha (p z)).
  apply:(can_inj (@form_includeK R Z R^o d)).
  rewrite form_reindex_include form_wedge_include.
  exact:(@alternating_unit_right R h2 Z R^o _ (scalar_bilinear R)
    1 (@mulr1 R) (form_include (A_m_dual (hom_as_linear p) (ta d alpha (p z))))).
rewrite hUnit in hTest.
have hPull:=@smooth_form_pullback_values R (m+n) m d AB A
  (EA d) (EC d) (va d) (vc d) p (PA d)
  (@SmoothFormPullback.laws R h2 (m+n) m d AB A hAB hA p ImageP PSmooth)
  (IA d alpha) z p hz
  (@current_cartesian_first_projection_differential R m n A B hA hB z hz).
exact:(eq_trans hTest (esym hPull)).
Qed.
End CurrentCartesianFirstCutoffValues.
