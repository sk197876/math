(** Federer (1969), 4.1.12, p. 368: choose
    a bounded smooth scalar test equal to
    one on a compact set, with its
    entire support in a given open neighbourhood.
    Reuse the original compact cutoff and
    scalar test realization; no interpolation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology NormOpenDomainLaws
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  AlternatingForms AlternatingZero CurrentZeroCovectorMaps CurrentSpaces CurrentSupportGeometry
  SmoothCompactSet SmoothCompactCutoffUP SmoothCompactCutoffSealed SmoothCutoffUnitRange
  CompactSupportFunctionUP CurrentScalarCompactFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBoundedNeighbourhoodTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (@current_test_space R h2 n Full hFull 0%N).

(** Source for [current_bounded_neighbourhood_test_exists]:
    for compact K inside open W there
    is an actual original zero-form test
    supported in W, with scalar values in
    [0,1] and value one on K. This
    supplies the bounded endpoint witnesses in
    Federer 4.1.12, p. 368, from
    the earlier partition and cutoff laws. *)
Theorem current_bounded_neighbourhood_test_exists (K:smooth_compact_set hNX Full) (W:set X):
  @open (real_norm_metric_space hNX) W->smooth_compact_carrier K `<=` W->
  exists gamma:DT,
    @current_test_support R h2 n 0%N Full hFull gamma `<=` W /\
    (forall x,0<=@current_zero_form_coefficient R n
      (@current_test_value R h2 n Full hFull 0%N gamma x)<=1) /\
    forall x,smooth_compact_carrier K x->
      @current_test_value R h2 n Full hFull 0%N gamma x=@zero_form R X R^o 1.
Proof.
move=>hW hKW.
have hWi:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:(open_nbhs_nbhs (conj hW hx)).
pose KW:=@Build_smooth_compact_set R X NX hNX W (smooth_compact_carrier K)
  hKW (smooth_compact_is_compact K).
pose chi:=@SmoothCompactCutoff.value R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) W KW hWi.
pose hChi:=@SmoothCompactCutoff.laws R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) W KW hWi.
have[psi [hPsi [hRange _]]]:=smooth_cutoff_unit_range_exists hChi.
pose C:=@Build_smooth_compact_set R X NX hNX Full
  (@real_function_support R (real_norm_metric_space hNX) psi) (fun _ _=>Logic.I)
  (smooth_cutoff_compact hPsi).
have[gamma [hValue hSupport]]:=@current_scalar_compact_function_exists R h2 n Full hFull C psi
  (smooth_cutoff_class hPsi) (fun x hx=>@real_function_zero_off_support R (real_norm_metric_space hNX) psi x hx).
exists gamma;split.
- exact:subset_trans hSupport (smooth_cutoff_support_in_domain hPsi).
- split.
  + move=>x;rewrite (hValue x Logic.I).
    change (is_true (0<=zero_form_value (@zero_form R X R^o (psi x))<=1)).
    rewrite zero_formK;exact:hRange x.
  + have[V [hV [hKV hOne]]]:=smooth_cutoff_neighbourhood_plateau hPsi.
    move=>x hx;rewrite (hValue x Logic.I) (hOne x (hKV x hx));by [].
Qed.
End CurrentBoundedNeighbourhoodTest.
