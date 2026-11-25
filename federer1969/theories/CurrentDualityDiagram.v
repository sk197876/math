(** Federer (1969), 4.1.7, p. 356:
    the full original smooth duality, divergence
    and current-boundary diagram, and its displayed
    integral pairing formula. All arrows are
    actual previously specified operators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal.
From Federer Require Import ExteriorDeterminant FiniteExteriorPowers AlternatingSum ScalarCoefficients BoundedHom HomogeneousHom GradedComponents Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorIndices FiniteCoordinates AlternatingForms
  AlternatingProduct AlternatingPairing CovectorProducts ExteriorHomogeneousProducts
  CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces CurrentDensityUP CurrentDensityAction
  CurrentDegreeTransport CurrentDualityCoefficients CurrentSmoothDuality CurrentSmoothDualityDifferential
  SmoothCurrentExteriorDerivative CurrentSmoothLebesgue CurrentSmoothLebesgueBoundary CurrentBoundary
  SummableRealFunctionUP MeasureIntegralUP EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentDualityDiagram.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Hypothesis hp:(p.+1<=n)%N.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation E := (@current_smooth_space R h2 n (fun _=>True) hFull (n-p.+1)).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull (n-p.+1)).
Local Notation L := (fun m=>@current_smooth_lebesgue_map R h2 n m).
Local Notation up := (@current_smooth_duality_upper R h2 n p.+1 hp (fun _=>True) hFull).
Local Notation hp0 := (leq_trans (leqnSn p) hp).
Local Notation up0 := (@current_smooth_duality_upper R h2 n p hp0 (fun _=>True) hFull).
Local Notation d := (@smooth_current_exterior_derivative R h2 n (n-p.+1) (fun _=>True) hFull).
Local Notation tr := (@current_smooth_degree_transport R h2 n (fun _=>True) hFull
  (n-p.+1).+1 (n-p) (subnSK hp)).

(** Source for [current_duality_lebesgue_diagram]:
    following D^(n-p) by the original
    Lebesgue-current map and -boundary is
    the same as following (-1)^(n-p)d
    by the next duality and current map,
    exactly Federer 4.1.7, p. 356.
    The original positive vector degree is p+1. *)
Theorem current_duality_lebesgue_diagram (phi:E):
  -@current_boundary R h2 n p (fun _=>True) hFull (L p.+1 (up phi))=
  (-1:R)^+(n-p.+1)*:L p (up0 (tr (d phi))).
Proof.
by rewrite current_smooth_lebesgue_boundary opprK current_smooth_duality_divergence linearZ.
Qed.

End CurrentDualityDiagram.

(** Source for [current_duality_lebesgue_pairing]:
    the displayed integrand equality pairs
    D^(n-p) phi with psi by evaluating
    phi wedge psi on e_top, Federer
    4.1.7, p. 356. The input form
    is an arbitrary original smooth form. *)
Theorem current_duality_lebesgue_pairing (R:realType) (h2:(1+1:R)!=0)
    n p (hp:(p<=n)%N)
    (phi:@current_smooth_space R h2 n (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) (n-p)) psi:
  let hFull:=fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) x in
  let L:=@current_smooth_lebesgue_map R h2 n p in
  let up:=@current_smooth_duality_upper R h2 n p hp (fun _=>True) hFull in
  let ev:=@current_smooth_value R h2 n (fun _=>True) hFull (n-p) in
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x=>
      alternating_wedge h2 (scalar_bilinear R) (form_include (ev phi x))
        (form_include (@current_test_value R h2 n (fun _=>True) hFull p psi x))
        (component_val (e_lambda (@coordinate_basis R n) (val (Lambda_top n))))))
    (@current_value R h2 n (fun _=>True) hFull p (L (up phi)) psi)%:E.
Proof.
move=>hFull L up ev.
have h:=@current_smooth_lebesgue_action R h2 n p (up phi) psi.
have hPoint:(fun x=>pairing (@current_vector_smooth_value R h2 n (fun _=>True) hFull p (up phi) x)
    (@current_test_value R h2 n (fun _=>True) hFull p psi x))=
  (fun x=>alternating_wedge h2 (scalar_bilinear R) (form_include (ev phi x))
    (form_include (@current_test_value R h2 n (fun _=>True) hFull p psi x))
    (component_val (e_lambda (@coordinate_basis R n) (val (Lambda_top n))))).
  apply:funext=>x.
  rewrite (@current_smooth_duality_upper_values R h2 n p hp (fun _=>True) hFull phi x Logic.I).
  exact:current_duality_upper_pairing.
by rewrite hPoint in h.
Qed.
