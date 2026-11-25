(** Federer (1969), 4.1.8, p. 360: identify the original
    separated test with the wedge of the two actual smooth
    pullbacks. This consequence of the independent point laws
    supports the printed boundary product rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear BilinearPrecompose RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients
  CurrentSpaces SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP
  SmoothFormPullbackSealed SmoothCurrentFormProduct SmoothCurrentFormProductBilinear
  CurrentCartesianDomain CurrentCartesianProjections CurrentCartesianSmoothProductUP CurrentCartesianTestProductSealed SmoothFunctionSpaceLaws CurrentDegreeTransport
  Alternating AlternatingZero AlternatingSum ExteriorHomogeneousProducts ZeroFormScalarProduct ComassWedgeSymmetry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianProjectionCutoffValues.
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

(** Source for [current_cartesian_projection_cutoff_values]:
    a scalar first-factor cutoff equal to one gives
    exactly the original second-projection pullback, supporting
    both compact-support projection formulas in Federer 4.1.8,
    p. 361. The scalar is the actual zero-form unit. *)
Theorem current_cartesian_projection_cutoff_values d (gamma:DA 0%N) (beta:DB d) z:
  AB z->@current_test_value R h2 m A hA 0%N gamma (p z)=@zero_form R X R^o 1->
  @current_test_value R h2 (m+n) AB hAB d
    (Tr _ _ (add0n d) (Pure 0 d gamma beta)) z=
    vc d (PB d (IB d beta)) z.
Proof.
move=>hz hGamma.
have hTest:=@current_test_degree_transport_values R h2 (m+n) AB hAB (0+d) d (add0n d)
  (Pure 0 d gamma beta) z.
have hPure:=(@CartesianTestProduct.laws R h2 m n A B hA hB 0%N d).2 gamma beta z hz.
rewrite hPure hGamma in hTest.
have hScalar:A_m_dual (hom_as_linear p) (@zero_form R X R^o 1)=@zero_form R Z R^o 1.
  apply:form_ext=>t;by rewrite A_m_dualE !zero_formE.
rewrite hScalar original_zero_form_wedge_scalar scale1r in hTest.
have hCast:form_reindex (add0n d) (A_m_dual (hom_as_linear q) (tb d beta (q z)))=
    A_m_dual (hom_as_linear q) (tb d beta (q z)).
  apply:(can_inj (@form_includeK R Z R^o d)).
  by rewrite form_reindex_include.
rewrite hCast in hTest.
have hPull:=@smooth_form_pullback_values R (m+n) n d AB B
  (EB d) (EC d) (vb d) (vc d) q (PB d)
  (@SmoothFormPullback.laws R h2 (m+n) n d AB B hAB hB q ImageQ QSmooth)
  (IB d beta) z q hz
  (@current_cartesian_last_projection_differential R m n A B hA hB z hz).
exact:(eq_trans hTest (esym hPull)).
Qed.
End CurrentCartesianProjectionCutoffValues.
