(** Federer (1969), 4.1.12, p. 367: the original
    flat seminorm of a smooth form is the maximum
    of its order-zero compact seminorm and that of
    its exterior derivative. The compact set is unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothCurrentExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFlatFormSeminormUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation Next := (@current_smooth_space R h2 n U hU m.+1).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation hNextD := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation nuNext := (smooth_function_derivative_seminorm hNextD).
Local Notation d := (@smooth_current_exterior_derivative R h2 n m U hU).

(** Source for [is_current_flat_form_seminorm]: the original
    displayed definition F_K(phi)=max(nu^0_K(phi),
    nu^0_K(d phi)), Federer 4.1.12, p. 367.
    Only this formula is specified; its seminorm laws
    and all dual statements remain proof obligations. *)
Definition is_current_flat_form_seminorm (K:smooth_compact_set hNX U) (p:E->R):Prop:=
  forall phi,p phi=Num.max (nu K 0%N phi) (nuNext K 0%N (d phi)).
End CurrentFlatFormSeminormUP.
