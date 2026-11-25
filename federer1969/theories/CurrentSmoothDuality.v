(** Federer (1969), 4.1.7, p. 356:
    the complementary dualities on the actual
    original smooth form and multivector spaces.
    The opaque target-operator interface realizes
    the already proved coefficient isomorphisms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentVectorSpaces CurrentDualityCoefficients SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothTargetOperatorUP SmoothTargetOperatorSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothDuality.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Hypothesis hp:(p<=n)%N.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o (n-p)).
Local Notation NY := (@current_form_comass R h2 n (n-p)).
Local Notation hNY := (@current_form_comass_real_norm R h2 n (n-p)).
Local Notation Z := (exterior_power X p).
Local Notation NZ := (@current_vector_mass R h2 n p).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n p).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU (n-p)).
Local Notation ev := (@current_smooth_value R h2 n U hU (n-p)).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU (n-p)).
Local Notation V := (@current_vector_smooth_space R h2 n U hU p).
Local Notation vv := (@current_vector_smooth_value R h2 n U hU p).
Local Notation hV := (@current_vector_smooth_space_laws R h2 n U hU p).
Local Notation lower := (@current_duality_lower_coefficient R h2 n p hp).
Local Notation upper := (@current_duality_upper_coefficient R h2 n p hp).

(** Source for [current_smooth_duality_lower]: the
    original D_p on actual smooth p-vector
    fields, supporting Federer 4.1.7, p. 356. *)
Definition current_smooth_duality_lower:Hom V E:=
  @SmoothTargetOperator.operator R X Z Y NX NZ NY hNX hNZ hNY U V E vv ev hV hE
    lower (@current_duality_lower_bounded R h2 n p hp).

(** Source for [current_smooth_duality_upper]: the
    original D^(n-p) on actual smooth
    (n-p)-forms, Federer 4.1.7, p. 356. *)
Definition current_smooth_duality_upper:Hom E V:=
  @SmoothTargetOperator.operator R X Y Z NX NY NZ hNX hNY hNZ U E V ev vv hE hV
    upper (@current_duality_upper_bounded R h2 n p hp).

(** Source for [current_smooth_duality_lower_values]:
    the actual lower map has precisely the
    original coefficient values, supporting Federer
    4.1.7, p. 356. *)
Lemma current_smooth_duality_lower_values xi x:U x->
  ev (current_smooth_duality_lower xi) x=lower (vv xi x).
Proof. exact:SmoothTargetOperator.laws. Qed.

(** Source for [current_smooth_duality_upper_values]:
    the actual upper map has precisely the
    original coefficient values, supporting Federer
    4.1.7, p. 356. *)
Lemma current_smooth_duality_upper_values phi x:U x->
  vv (current_smooth_duality_upper phi) x=upper (ev phi x).
Proof. exact:SmoothTargetOperator.laws. Qed.

(** Source for [current_smooth_duality_lower_upper_cancel]:
    complementary actual smooth spaces are
    isomorphic by the original maps, supporting
    every form in Federer's diagram,
    4.1.7, p. 356. *)
Lemma current_smooth_duality_lower_upper_cancel:
  cancel current_smooth_duality_lower current_smooth_duality_upper.
Proof.
move=>xi;apply:(smooth_function_extensional hV)=>x hx.
rewrite current_smooth_duality_upper_values // current_smooth_duality_lower_values //.
exact:current_duality_lower_upper_cancel.
Qed.

(** Source for [current_smooth_duality_upper_lower_cancel]:
    every original smooth complementary form is
    in the image of D_p, supporting the
    original diagram in Federer 4.1.7, p. 356. *)
Lemma current_smooth_duality_upper_lower_cancel:
  cancel current_smooth_duality_upper current_smooth_duality_lower.
Proof.
move=>phi;apply:(smooth_function_extensional hE)=>x hx.
rewrite current_smooth_duality_lower_values // current_smooth_duality_upper_values //.
exact:current_duality_upper_lower_cancel.
Qed.
End CurrentSmoothDuality.
