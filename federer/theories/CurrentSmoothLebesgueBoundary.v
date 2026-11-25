(** Federer (1969), 4.1.7, p. 356:
    the right square of the original smooth
    diagram is the actual C1 integration-by-parts
    theorem, specialized to the original smooth
    multivector spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormClassOneUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces
  CurrentDensityUP CurrentDensityAction CurrentDensityArithmetic CurrentDensityUniqueness CurrentSmoothLebesgue
  CurrentClassOneDivergence CurrentLebesgueBoundary CurrentBoundary CurrentDivergenceMap SmoothCurrentDivergence
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothGlobalFirstDifferential EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothLebesgueBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (exterior_power X p.+1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_vector_mass R h2 n p.+1).
Local Notation hNY := (@current_vector_mass_real_norm R h2 n p.+1).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n (fun _=>True) hFull m).
Local Notation vv := (fun m=>@current_vector_smooth_value R h2 n (fun _=>True) hFull m).
Local Notation hV := (fun m=>@current_vector_smooth_space_laws R h2 n (fun _=>True) hFull m).
Local Notation D := (@current_vector_smooth_derivatives R h2 n (fun _=>True) hFull p.+1).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n (fun _=>True) hFull p.+1).
Local Notation L := (fun m=>@current_smooth_lebesgue_map R h2 n m).
Local Notation div := (@smooth_current_divergence R h2 n p (fun _=>True) hFull).
Local Notation mu := (@euclidean_lebesgue_measure R n).

(** Source for [current_smooth_lebesgue_boundary]:
    boundary(Lebesgue wedge xi)=-Lebesgue
    wedge div xi on the actual original
    spaces, Federer 4.1.7, p. 356.
    Every positive input degree is included. *)
Theorem current_smooth_lebesgue_boundary (xi:V p.+1):
  @current_boundary R h2 n p (fun _=>True) hFull (L p.+1 xi)=-L p (div xi).
Proof.
pose DXi:=@smooth_global_first_differential R X Y NX NY hNX hNY
  (V p.+1) D xi.
have hXi:=@smooth_global_first_differential_class_one R X Y NX NY hNX hNY
  (V p.+1) (vv p.+1) (hV p.+1) D hD xi.
have hAction:=@current_lebesgue_boundary_action R h2 n p (vv p.+1 xi) DXi (L p.+1 xi)
  (current_smooth_lebesgue_action xi) hXi.
have hDivField:vv p (div xi)=@current_class_one_divergence_field R h2 n p DXi.
  apply:funext=>x;rewrite (@smooth_current_divergence_values R h2 n p (fun _=>True) hFull xi x Logic.I).
  by [].
apply:(@current_density_action_unique R h2 n p mu (fun x=>-vv p (div xi) x)).
- by rewrite hDivField.
- have hScaled:=@current_density_scaled_action R h2 n p mu (euclidean_lebesgue_is_measure R n)
    (vv p (div xi)) (L p (div xi)) (-1) (current_smooth_lebesgue_action (div xi)).
  have hField:(fun x=>(-1)*:vv p (div xi) x)=(fun x=>-vv p (div xi) x).
    apply:funext=>x;exact:scaleN1r.
  by rewrite hField scaleN1r in hScaled.
Qed.
End CurrentSmoothLebesgueBoundary.
