(** Federer (1969), 4.1.7, p. 356: the
    first current identity follows from d squared
    zero on the actual original test forms. Reuse
    the complete twice-differentiable theorem of 4.1.6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP SmoothTestSpaces
  LinearSubspaceRepresentationUP CurrentCoefficientNorms CurrentFormInducedNorm CurrentSpaces
  CurrentExteriorDifferentialMap SmoothCurrentExteriorDerivative CurrentTestExteriorDerivative
  ExteriorDerivativeUP ExteriorDerivativeSquared.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentExteriorDerivativeSquared.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (@current_form_comass R h2 n m.+1).
Local Notation hNZ := (@current_form_comass_real_norm R h2 n m.+1).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation fv := (@current_smooth_value R h2 n U hU m.+1).
Local Notation gv := (@current_smooth_value R h2 n U hU m.+2).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hF := (@current_smooth_space_laws R h2 n U hU m.+1).
Local Notation hG := (@current_smooth_space_laws R h2 n U hU m.+2).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation eZ := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation L := (@current_exterior_differential_map R h2 n m).
Local Notation P := (@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation Q := (@smooth_current_exterior_derivative R h2 n m.+1 U hU).

(** Source for [smooth_current_exterior_derivative_total_values]:
    exact equality of the actual normalized field
    representatives, supporting Federer 4.1.7, p. 356. *)
Lemma smooth_current_exterior_derivative_total_values f:
  fv (P f)=(fun x=>L (@D 1%N x f)).
Proof.
apply:funext=>x; case:(pselect (U x))=>[hx|hx].
- exact:(@smooth_current_exterior_derivative_values R h2 n m U hU f x hx).
- by rewrite (smooth_function_evaluation_outside hF _ hx)
    (smooth_derivative_outside hD 1%N f hx) linear0.
Qed.

(** Source for [smooth_current_exterior_derivative_squared]:
    d squared zero holds on the actual original
    smooth form spaces, supporting the first current
    identity in Federer 4.1.7, p. 356. *)
Theorem smooth_current_exterior_derivative_squared (f:E):Q (P f)=0.
Proof.
apply:(smooth_function_extensional hG)=>x hx; rewrite (smooth_function_zero_value hG).
have hZero:=@exterior_derivative_squared_at R h2 n R^o NX (fun c:R^o=>`|c|)
  hNX (@scalar_absolute_value_norm R) m NY NZ hNY
  (@current_form_comass_is_induced R h2 n m) (@current_form_comass_is_induced R h2 n m.+1)
  Z eZ ZN hZ U (ev f) (fun y=>@D 1%N y f) x (@D 2%N x f)
  (fun y hy=>@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 1%N f y hy)
  (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 2%N f x hx).
change (has_exterior_derivative NX NZ U (fun y=>L (@D 1%N y f)) x 0) in hZero.
rewrite -(smooth_current_exterior_derivative_total_values f) in hZero.
exact:(@exterior_derivative_unique R X R^o NX hNX m.+1 NZ hNZ U (fv (P f)) x
  (gv (Q (P f)) x) 0 (@smooth_current_exterior_derivative_actual R h2 n m.+1 U hU (P f) x hx) hZero).
Qed.

(** Source for [current_test_exterior_derivative_squared]:
    d squared zero on the actual original test
    forms, supporting Federer 4.1.7, p. 356. *)
Theorem current_test_exterior_derivative_squared (f:@current_test_space R h2 n U hU m):
  @current_test_exterior_derivative R h2 n m.+1 U hU
    (@current_test_exterior_derivative R h2 n m U hU f)=0.
Proof.
apply:(subspace_representation_injective (smooth_test_space_laws hG)).
rewrite (@current_test_exterior_derivative_inclusion R h2 n m.+1 U hU)
  (@current_test_exterior_derivative_inclusion R h2 n m U hU).
by rewrite smooth_current_exterior_derivative_squared linear0.
Qed.
End CurrentExteriorDerivativeSquared.
