(** Federer (1969), 4.1.12, p. 367: the
    scalar factor and its differential vanish off
    its original support. Reuse the derivative-locality
    theorem already proved for the original smooth
    spaces in 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothFunctionSupport SmoothLocalSupport SmoothCurrentExteriorDerivative CurrentExteriorDifferentialMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentFormSupportValues.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation NextValue := (@current_smooth_value R h2 n U hU m.+1).
Local Notation d := (@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).

(** Source for [current_form_value_outside_support]: an
    original smooth form vanishes off its relative
    support, supporting the smaller compact index in
    Federer 4.1.12, p. 367. *)
Lemma current_form_value_outside_support (phi:E) x:
  U x->~support phi x->ev phi x=0.
Proof.
move=>hx hOutside;apply:contrapT=>hNonzero;apply:hOutside.
exact:(@smooth_function_nonzero_in_support R X Y NX hNX U E ev phi x hx hNonzero).
Qed.

(** Source for [current_form_exterior_outside_support]:
    the actual exterior differential vanishes off the
    original support, supporting the exact multiplier
    estimate in Federer 4.1.12, p. 367. *)
Lemma current_form_exterior_outside_support (phi:E) x:
  U x->~support phi x->NextValue (d phi) x=0.
Proof.
move=>hx hOutside.
have hZero:=@smooth_derivative_outside_support R X Y NX NY hNX hNY U hU E ev D hD
  phi x hx hOutside 1%N.
by rewrite (@smooth_current_exterior_derivative_values R h2 n m U hU phi x hx) hZero linear0.
Qed.
End CurrentFormSupportValues.
