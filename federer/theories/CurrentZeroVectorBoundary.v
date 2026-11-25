(** Federer (1969), 4.1.7, p. 356: the
    eighth displayed identity for the boundary
    of a zero-current times a positive-degree
    smooth vector field. The proof combines
    the preceding coordinate and product identities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import CurrentBoundary Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms ExteriorGrading
  AlternatingForms AlternatingZero CurrentSpaces CurrentVectorSpaces CurrentEvaluation CurrentPointEvaluation
  CurrentZeroVectorProduct CurrentPositiveContraction CurrentDirectionalDerivative CurrentVectorDirectionalDerivative
  SmoothCurrentOneCovector SmoothCurrentDivergence SmoothCurrentDivergenceCoordinates
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentZeroVectorBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun k=>@current_space R h2 n U hU k).
Local Notation V := (fun k=>@current_vector_smooth_space R h2 n U hU k).
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation zp := (fun k=>@current_zero_vector_product R h2 n k U hU).
Local Notation zi := (fun k=>@current_zero_test_vector_interior R h2 n k U hU).
Local Notation pc := (@current_positive_one_contraction R h2 n p U hU).
Local Notation cut := (@smooth_current_one_covector R h2 n p U hU).
Local Notation dir := (fun j=>@current_directional_derivative R h2 n 0 U hU (@coordinate_basis R n j)).
Local Notation vdir := (fun j=>@current_vector_smooth_directional_derivative R h2 n p.+1 U hU
  (@coordinate_basis R n j)).

(** Source for [current_zero_positive_contraction]:
    contraction of T wedge xi by a
    constant one-covector equals T wedge the
    contracted field when dim T=0,
    supporting the eighth equation in Federer
    4.1.7, p. 356, by the seventh. *)
Theorem current_zero_positive_contraction (T:C 0) (xi:V p.+1) alpha:
  pc alpha (zp p.+1 xi T)=zp p (cut alpha xi) T.
Proof.
apply:(@current_values_extensional R h2 n p U hU)=>psi.
rewrite current_positive_one_contraction_evaluation !current_zero_vector_product_evaluation.
congr (@current_value R h2 n U hU 0 T _).
apply:(smooth_test_values_extensional hE0)=>x hx.
change (@current_test_value R h2 n U hU 0%N
    (zi p.+1 xi (@current_positive_test_wedge R h2 n p U hU alpha psi)) x=
  @current_test_value R h2 n U hU 0%N (zi p (cut alpha xi) psi) x).
apply:(can_inj (@zero_form_valueK R X R^o)).
rewrite !current_zero_test_vector_values // smooth_current_one_covector_values //.
exact:current_positive_test_wedge_pairing.
Qed.

(** Source for [current_zero_vector_boundary]:
    boundary(T wedge xi)=-T wedge div xi
    -sum_j (D_j T) wedge (xi contracted DX_j),
    Federer 4.1.7, p. 356, eighth
    displayed equation. T is any zero-current;
    no integration representation is assumed. *)
Theorem current_zero_vector_boundary (T:C 0) (xi:V p.+1):
  @current_boundary R h2 n p U hU (zp p.+1 xi T)=
    -zp p (@smooth_current_divergence R h2 n p U hU xi) T-
      \sum_j zp p (cut (euclidean_coordinate_form j) xi) (dir j T).
Proof.
rewrite current_positive_boundary_coordinates.
have hTerm j:pc (euclidean_coordinate_form j)
    (@current_directional_derivative R h2 n p.+1 U hU (@coordinate_basis R n j) (zp p.+1 xi T))=
    zp p (cut (euclidean_coordinate_form j) xi) (dir j T)+
    zp p (cut (euclidean_coordinate_form j) (vdir j xi)) T.
  pose alpha:=@euclidean_coordinate_form R n j.
  pose A0:=zp p.+1 xi (dir j T).
  pose B0:=zp p.+1 (vdir j xi) T.
  have hProduct:=@current_zero_vector_directional_product R h2 n p.+1 U hU
    (@coordinate_basis R n j) T xi.
  have hAdd:pc alpha (A0+B0)=pc alpha A0+pc alpha B0 by rewrite linearD.
  have hSplit:=eq_trans (congr1 (pc alpha) hProduct) hAdd.
  have hA:pc alpha A0=zp p (cut alpha xi) (dir j T):=
    @current_zero_positive_contraction (dir j T) xi alpha.
  have hB:pc alpha B0=zp p (cut alpha (vdir j xi)) T:=
    @current_zero_positive_contraction T (vdir j xi) alpha.
  exact (eq_trans hSplit (congr2 (fun a b:C p=>a+b) hA hB)).
have hSum:(\sum_j pc (euclidean_coordinate_form j)
    (@current_directional_derivative R h2 n p.+1 U hU (@coordinate_basis R n j) (zp p.+1 xi T)))=
    (\sum_j zp p (cut (euclidean_coordinate_form j) xi) (dir j T))+
    (\sum_j zp p (cut (euclidean_coordinate_form j) (vdir j xi)) T).
  rewrite -big_split;apply:eq_bigr=>j _;exact:hTerm.
have hDiv:(\sum_j zp p (cut (euclidean_coordinate_form j) (vdir j xi)) T)=
    zp p (@smooth_current_divergence R h2 n p U hU xi) T.
  have hField:=@smooth_current_divergence_coordinate_formula R h2 n p U hU xi.
  have hApplied:=congr1 (@current_zero_vector_field_product R h2 n p U hU T) hField.
  rewrite linear_sum in hApplied.
  exact:esym hApplied.
by rewrite hSum hDiv opprD addrC.
Qed.
End CurrentZeroVectorBoundary.
