(** Federer (1969), 4.1.14, pp. 370–371: tests on
    the original source have representatives on a neighbourhood
    of K with the same action on currents supported in K and
    no larger original flat seminorm. Use the preceding compact
    scalar plateau and actual test zero-extension range. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingZero AlternatingProduct
  ScalarCoefficients ZeroFormScalarProduct CurrentSpaces CurrentCoefficientNorms
  SmoothCompactSet SmoothFunctionSupport SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces
  SmoothTestEvaluation CurrentSupportGeometry CurrentFormSupportValues
  CurrentNeighbourhoodCutoff CurrentTestFormProduct CurrentTestExteriorDerivative
  SmoothCurrentExteriorDerivative
  CurrentTestExteriorPlateau CurrentScalarProductDerivativeValues
  CurrentTestNearSupportAgreement CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentFlatFormSeminormLaws CurrentFlatTestPointBounds CurrentFlatTestLeastBound
  CurrentFlatOpenTestExtension CurrentLipschitzCompactImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatTestNeighbourhood.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y d := (A_m X R^o d).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY d := (@current_form_comass R h2 n d).
Local Notation hNY d := (@current_form_comass_real_norm R h2 n d).
Variables U Z:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hZU:forall x,Z x->U x.
Variable K:smooth_compact_set hNX U.
Hypothesis hKZ:smooth_compact_carrier K `<=` Z.
Local Notation KZ := (@current_compact_index_in_open R n U Z K hKZ).
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation sv d := (@current_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_smooth_space_laws R h2 n U hU d).
Local Notation DU d := (@current_test_space R h2 n U hU d).
Local Notation DZ d := (@current_test_space R h2 n Z hZ d).
Local Notation tv d := (@current_test_value R h2 n U hU d).
Local Notation inc d := (smooth_test_inclusion (hE d)).
Local Notation td d := (@current_test_exterior_derivative R h2 n d U hU).
Local Notation sd d := (@smooth_current_exterior_derivative R h2 n d U hU).
Local Notation extension := (@current_open_test_extension R h2 n m Z U hZ hU hZU).
Local Notation FU := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation FZ := (@current_flat_test_seminorm R h2 n m Z hZ KZ).
Local Notation CU := (@current_space R h2 n U hU m).

(** Source for [current_flat_test_neighbourhood_representative]:
    every original test has a smaller-source test with the
    same action on every current supported in K and a no
    larger F_K. This supplies the reverse source comparison
    in Federer 4.1.14, pp. 370–371, by the original
    scalar plateau and support laws of 4.1.12, p. 368.
    No current, finite-mass or nonempty-set premise is added. *)
Theorem current_flat_test_neighbourhood_representative (phi:DU m):
  exists psi:DZ m,
    (forall T:CU,@current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
      @current_value R h2 n U hU m T (extension psi)=
        @current_value R h2 n U hU m T phi) /\FZ psi<=FU phi.
Proof.
have hOpenZ:@open (real_norm_metric_space hNX) Z.
  rewrite openE=>x hx.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX Z x).1 (@hZ x hx)).
have[gamma [hGamma [W [hW [hKW [hWZ hOne]]]]]]:=
  @current_neighbourhood_scalar_cutoff R h2 n U hU K Z hOpenZ hKZ hZU.
pose chi:=@current_test_form_product R h2 n 0%N m U hU (inc 0%N gamma) phi.
have hOneSmooth x (hx:W x):sv 0%N (inc 0%N gamma) x=@zero_form R X R^o 1.
  exact:(hOne x hx).
have hWU:W `<=` U by move=>x hx;exact:hZU x (hWZ x hx).
have hValue x:W x->tv m chi x=tv m phi x.
  move=>hx;rewrite /chi (@current_test_form_product_values R h2 n 0%N m
    U hU (inc 0%N gamma) phi x (hWU x hx)).
  by rewrite (hOneSmooth x hx) original_zero_form_wedge_scalar scale1r.
have hDerivative x:W x->tv m.+1 (td m chi) x=tv m.+1 (td m phi) x.
  move=>hx.
  have hDgamma:=@current_test_exterior_plateau_zero R h2 n U hU gamma W
    (@zero_form R X R^o 1) hW hWU hOne x hx.
  have hDgammaSmooth:sv 1%N (sd 0%N (inc 0%N gamma)) x=0.
    rewrite -(@current_test_exterior_derivative_inclusion R h2 n 0%N U hU gamma).
    exact:hDgamma.
  rewrite /chi (@current_scalar_product_derivative_values R h2 n m U hU
    (inc 0%N gamma) phi x (hWU x hx)) hDgammaSmooth (hOneSmooth x hx).
  rewrite (bil0l (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) 1%N m))
    add0r original_zero_form_wedge_scalar scale1r.
  by [].
pose Lgamma:=@Build_smooth_compact_set R X NX hNX U
  (@current_test_support R h2 n 0%N U hU gamma) (fun x hx=>hx.1)
  (@smooth_test_support_compact R X (Y 0%N) NX (NY 0%N) hNX (hNY 0%N)
    U (E 0%N) (sv 0%N) (hE 0%N) gamma).
have hChiSupport:@current_test_support R h2 n m U hU chi
    `<=` smooth_compact_carrier Lgamma.
  change (@smooth_function_support R X (Y m) NX hNX U (E m) (sv m) (inc m chi)
    `<=` smooth_compact_carrier Lgamma).
  apply:(@smooth_function_compact_support_iff R X (Y m) NX (NY m) hNX (hNY m)
    U (E m) (sv m) (hE m) Lgamma (inc m chi)).2=>x hx.
  case:(pselect (U x))=>hUx.
  - have hGammaZero:=@current_form_value_outside_support R h2 n 0%N U hU
      (inc 0%N gamma) x hUx hx.
    change (tv m chi x=0).
    rewrite /chi (@current_test_form_product_values R h2 n 0%N m U hU
      (inc 0%N gamma) phi x hUx) hGammaZero.
    exact:(bil0l (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) 0%N m) _).
  - exact:(@smooth_function_evaluation_outside R X (Y m) NX (NY m) hNX (hNY m)
      U (E m) (sv m) (hE m) (inc m chi) x hUx).
have hChiZ:@current_test_support R h2 n m U hU chi `<=` Z.
  move=>x hx;exact:hGamma x (hChiSupport x hx).
have[psi hExtended]:=@current_open_test_extension_supported_range R h2 n m
  Z U hZ hU hZU chi hChiZ.
exists psi;split.
- move=>T hT;rewrite hExtended.
  apply:(@current_test_near_support_values_equal R h2 n m U hU T chi phi W hW).
  + move=>x hx;exact:hKW x (hT x hx).
  + exact:hValue.
- rewrite -(@current_open_test_flat_seminorm R h2 n m U Z hU hZ hZU K hKZ psi)
    hExtended.
  apply:(@current_flat_test_least_pointwise_bound R h2 n m U hU K chi
    (FU phi) (real_seminorm_nonnegative
      (@current_flat_test_is_seminorm R h2 n m U hU K) phi))=>x hx;split.
  + rewrite (hValue x (hKW x hx)).
    exact:(@current_flat_test_point_bound R h2 n m U hU K phi x hx).
  + rewrite (hDerivative x (hKW x hx)).
    exact:(@current_flat_test_derivative_point_bound R h2 n m U hU K phi x hx).
Qed.
End CurrentFlatTestNeighbourhood.
