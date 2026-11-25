(** Federer (1969), 4.1.7, p. 356: the
    boundary of a class-one Lebesgue-density
    current is minus the current of its
    actual divergence. Reuse the original
    coordinate boundary identity and 4.1.1
    integration by parts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import AlternatingPairing Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanCoordinateForms ExteriorGrading OneCovectorInterior CurrentCoefficientNorms CurrentSpaces
  CurrentDensityUP CurrentDensityAction CurrentDensityArithmetic CurrentDensityUniqueness CurrentLebesgueDensity
  CurrentBoundary CurrentDirectionalDerivative CurrentPositiveContraction CurrentClassOneDivergence
  CurrentOneCovectorMap DivergenceCoordinates EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentLebesgueBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation V := (exterior_power X p.+1).
Local Notation VN := (@current_vector_mass R h2 n p.+1).
Local Notation C := (fun m=>@full_current_space R h2 n m).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation pc := (@current_positive_one_contraction R h2 n p (fun _=>True) hFull).
Local Notation div := (@current_class_one_divergence_field R h2 n p).

(** Source for [current_positive_contraction_density_action]:
    fixed one-covector contraction transports the
    original density by the actual left
    interior, supporting the boundary formula in
    Federer 4.1.7, p. 356. *)
Theorem current_positive_contraction_density_action gamma (xi:X->V) (T:C p.+1) alpha:
  is_current_density_action gamma xi T ->
  is_current_density_action gamma (fun x=>positive_one_covector_interior h2 (xi x) alpha)
    (pc alpha T).
Proof.
move=>hT psi.
have h:=hT (@current_positive_test_wedge R h2 n p (fun _=>True) hFull alpha psi).
have hEq:(fun x=>pairing (xi x)
    (@current_test_value R h2 n (fun _=>True) hFull p.+1
      (@current_positive_test_wedge R h2 n p (fun _=>True) hFull alpha psi) x))=
  (fun x=>pairing (positive_one_covector_interior h2 (xi x) alpha)
    (@current_test_value R h2 n (fun _=>True) hFull p psi x)).
  apply:funext=>x;exact:current_positive_test_wedge_pairing Logic.I.
rewrite hEq in h;rewrite current_positive_one_contraction_evaluation;exact:h.
Qed.

(** Source for [current_lebesgue_boundary_action]:
    the original boundary acts by integration
    against minus div xi for a class-one
    density, Federer 4.1.7, p. 356. *)
Theorem current_lebesgue_boundary_action (xi:X->V) (DXi:X->Hom X V) (T:C p.+1):
  is_current_density_action mu xi T ->
  is_norm_class_one_field NX VN (fun _=>True) xi DXi ->
  is_current_density_action mu (fun x=>-div DXi x)
    (@current_boundary R h2 n p (fun _=>True) hFull T).
Proof.
move=>hT hXi.
pose D j:=@current_directional_derivative R h2 n p.+1 (fun _=>True) hFull
  (@coordinate_basis R n j) T.
pose Q j:=pc (euclidean_coordinate_form j) (D j).
pose eta j x:=positive_one_covector_interior h2 (DXi x (@coordinate_basis R n j))
  (euclidean_coordinate_form j).
have hEach j:is_current_density_action mu (eta j) (Q j).
  apply:current_positive_contraction_density_action.
  exact:(@current_lebesgue_directional_action R h2 n p.+1 xi DXi
    (@coordinate_basis R n j) T hT hXi).
have hSum:=@current_density_finite_sum_action R h2 n p mu hm [the finType of 'I_n] eta Q hEach.
have hNegative:=@current_density_scaled_action R h2 n p mu hm
  (fun x=>\sum_j eta j x) (\sum_j Q j) (-1) hSum.
have hField:(fun x=>(-1)*:(\sum_j eta j x))=(fun x=>-div DXi x).
  apply:funext=>x;by rewrite scaleN1r /div /current_class_one_divergence_field divergence_coordinate_formula.
rewrite hField scaleN1r in hNegative.
rewrite -(@current_positive_boundary_coordinates R h2 n p (fun _=>True) hFull T) in hNegative.
exact:hNegative.
Qed.

(** Source for [current_lebesgue_boundary]: the
    original equality boundary(Lebesgue wedge xi)
    =-Lebesgue wedge div xi, Federer
    4.1.7, p. 356. Actual class-one
    continuity proves the required local integrability;
    no extra regularity premise is imposed. *)
Theorem current_lebesgue_boundary (xi:X->V) (DXi:X->Hom X V)
    (hXi:is_norm_class_one_field NX VN (fun _=>True) xi DXi):
  @current_boundary R h2 n p (fun _=>True) hFull
    (@current_lebesgue_density R h2 n p.+1 xi
      (@continuous_current_density_integrable R h2 n p.+1 xi (norm_class_one_zero hXi)))=
  -@current_lebesgue_density R h2 n p (div DXi)
    (@continuous_current_density_integrable R h2 n p (div DXi)
      (@current_class_one_divergence_continuous R h2 n p (fun _=>True) xi DXi hXi)).
Proof.
apply:(@current_density_action_unique R h2 n p mu (fun x=>-div DXi x)).
- apply:(@current_lebesgue_boundary_action xi DXi
    (@current_lebesgue_density R h2 n p.+1 xi
      (@continuous_current_density_integrable R h2 n p.+1 xi (norm_class_one_zero hXi)))
    _ hXi).
  exact:current_lebesgue_density_action.
- have h:=@current_density_scaled_action R h2 n p mu hm (div DXi)
    (@current_lebesgue_density R h2 n p (div DXi)
      (@continuous_current_density_integrable R h2 n p (div DXi)
        (@current_class_one_divergence_continuous R h2 n p (fun _=>True) xi DXi hXi))) (-1)
    (current_lebesgue_density_action _).
  have hEq:(fun x=>(-1)*:div DXi x)=(fun x=>-div DXi x).
    apply:funext=>x;exact:scaleN1r.
  by rewrite hEq scaleN1r in h.
Qed.
End CurrentLebesgueBoundary.
