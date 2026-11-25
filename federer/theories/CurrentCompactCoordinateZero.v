(** Federer (1969), 4.1.20, p. 378, final displayed
    equality and conclusion: zero action on every scalar
    multiple of every coordinate form implies that the
    current is zero. Reuse the actual finite test expansion
    of 4.1.7, p. 356, rather than choosing a new model of
    currents or assuming a measure representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom Bilinear ScalarCoefficients RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorIndices FiniteCoordinates CovectorProducts EuclideanCoordinateForms
  AlternatingForms AlternatingZero AlternatingProduct ExteriorHomogeneousProducts
  ZeroFormScalarProduct CurrentSpaces CurrentEvaluation CurrentPointEvaluation CurrentConstantFields
  CurrentDegreeTransport CurrentDegreeTransportInverse CurrentTestCoordinateExpansion
  CurrentTestFormProduct CurrentScalarFormProduct SmoothCurrentFormProduct
  CurrentCompactSmoothValue SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CoordinateZero.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E:=(fun j=>@current_smooth_space R h2 n U hU j).
Local Notation hE:=(fun j=>@current_smooth_space_laws R h2 n U hU j).
Local Notation DT:=(fun j=>@current_test_space R h2 n U hU j).
Local Notation cf:=(@current_constant_form R h2 n U hU).
Local Notation wl:=(@omega_lambda R h2 X n (@euclidean_coordinate_form R n) m).
Local Notation Tr:=(@current_test_degree_transport R h2 n U hU (m+0) m (addn0 m)).
Local Notation BackTest:=(@current_test_degree_transport R h2 n U hU m (m+0) (esym (addn0 m))).
Local Notation P:=(@current_test_form_product R h2 n m 0%N U hU).
Local Notation ScalarProduct:=(@smooth_current_form_product R h2 n 0%N m U hU).
Variable T:@current_space R h2 n U hU m.
Hypothesis hCompact:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T).
Local Notation action:=(@current_compact_smooth_value R h2 n m U hU T hCompact).

(** Source for [current_compact_coordinate_zero]: the last
    step in Federer 4.1.20, p. 378, from the original
    coordinate expansion in 4.1.7. The scalar fields and
    original tests are arbitrary. Empty domains, degree zero
    and the empty coordinate family above dimension remain. *)
Theorem current_compact_coordinate_zero:
  (forall (lambda:Lambda n m) (gamma:E 0%N),
    action (ScalarProduct gamma (cf m (wl lambda)))=0)->T=0.
Proof.
move=>hZero;apply:(@current_values_extensional R h2 n m U hU)=>psi.
have hBack:Tr (BackTest psi)=psi.
  have h:=@current_test_degree_transport_inverse R h2 n U hU
    m (m+0) (esym (addn0 m)) psi.
  have hProof:esym (esym (addn0 m))=addn0 m:=Prop_irrelevance _ _.
  by rewrite hProof in h.
have hExpansion:=@current_test_coordinate_expansion R h2 n m U hU (BackTest psi).
rewrite hBack in hExpansion.
have hTerm (lambda:Lambda n m) (gamma:DT 0%N):
    @current_value R h2 n U hU m T (Tr (P (cf m (wl lambda)) gamma))=0.
  pose scalar:=smooth_test_inclusion (hE 0%N) gamma.
  have hSmooth:smooth_test_inclusion (hE m) (Tr (P (cf m (wl lambda)) gamma))=
      ScalarProduct scalar (cf m (wl lambda)).
    apply:(smooth_function_extensional (hE m))=>x hx.
    change (@current_test_value R h2 n U hU m
        (Tr (P (cf m (wl lambda)) gamma)) x=
      @current_smooth_value R h2 n U hU m
        (ScalarProduct scalar (cf m (wl lambda))) x).
    rewrite (@current_test_degree_transport_values R h2 n U hU
      (m+0) m (addn0 m))
      (@current_test_form_product_values R h2 n m 0%N U hU
        (cf m (wl lambda)) gamma x hx)
      (@smooth_current_form_product_values R h2 n 0%N m U hU
        scalar (cf m (wl lambda)) x hx)
      (@current_constant_form_values R h2 n U hU m (wl lambda) x hx).
    change (form_reindex (addn0 m)
        (form_wedge h2 (scalar_bilinear R) (wl lambda)
          (@current_test_value R h2 n U hU 0%N gamma x))=
      form_wedge h2 (scalar_bilinear R)
        (@current_test_value R h2 n U hU 0%N gamma x) (wl lambda)).
    rewrite -{1 2}(zero_form_valueK
      (@current_test_value R h2 n U hU 0%N gamma x)).
    by rewrite current_form_wedge_zero_scalar original_zero_form_wedge_scalar.
  rewrite -(@current_compact_smooth_test_value R h2 n m U hU
    T hCompact (Tr (P (cf m (wl lambda)) gamma))) hSmooth.
  exact:hZero lambda scalar.
rewrite hExpansion linear_sum.
rewrite (linear0 (@current_value R h2 n U hU m)) hom_zeroE.
apply:big1=>lambda _;exact:hTerm.
Qed.
End CoordinateZero.
