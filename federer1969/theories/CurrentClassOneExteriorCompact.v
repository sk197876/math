(** Federer (1969), 4.1.7, p. 358:
    a compact class-one form and its
    actual exterior derivative have one
    compact support bound. Reuse the
    original local differential and bounded
    alternation; no smooth approximation is
    assumed in this supporting assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormClassOneUP NormClassOneDirectionalField NormRegularity NormHigherDifferentialFirst
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  SmoothCompactSet ExteriorDerivativeUP ExteriorDifferentialUP ExteriorDifferentialSealed
  CurrentCoefficientNorms CurrentClassOneExterior.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentClassOneExteriorCompact.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation Z := (A_m X R^o m.+1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (@current_form_comass R h2 n m.+1).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ej := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).

(** Source for [current_class_one_exterior_compact]:
    the original compact class-one form
    has a continuous actual exterior derivative
    vanishing off the same K, supporting
    the approximation argument for Federer
    4.1.7, p. 358. *)
Theorem current_class_one_exterior_compact (K:smooth_compact_set hNX (fun _=>True)) (phi:X->Y):
  norm_class hNX hNY (fun _=>True) phi 1%N->
  (forall x,~smooth_compact_carrier K x->phi x=0)->
  exists beta:X->Z,norm_class_zero NX NZ (fun _=>True) beta /\
    (forall x,has_exterior_derivative NX NY (fun _=>True) phi x (beta x)) /\
    forall x,~smooth_compact_carrier K x->beta x=0.
Proof.
move=>hClass hOff.
have [beta [hContinuous hExterior]]:=@current_class_one_exterior_continuous R h2 n m
  (fun _=>True) phi hClass.
exists beta;split=>//;split;first by move=>x;exact:hExterior x Logic.I.
have [_ [D [hActual hDerivativeContinuous]]]:=hClass.
pose L x:=@continuous_multilinear_one_operator R X Y (J 1%N) NX NY
  (@ej 1%N) (@JN 1%N) (hJ 1%N) (D x).
have hDifferential x:has_norm_differential NX NY (fun _=>True) phi x (L x).
  exact:((@norm_higher_differential_first R X Y NX NY hNX hNY J ej JN hJ
    (fun _=>True) phi x (D x)).1 (hActual x Logic.I)).
move=>x hx.
have hZero:=@norm_differential_zero_off_compact R X Y NX NY hNX hNY K phi L
  hOff hDifferential x hx.
have [M [hM hExteriorValue]]:=hExterior x Logic.I.
have hSame:=norm_differential_unique hNX hNY hM (hDifferential x).
rewrite hZero in hSame;rewrite hSame in hExteriorValue.
have hValue:=exterior_differential_value_unique hExteriorValue
  (@ExteriorDifferential.laws R h2 n R^o m 0).
rewrite hValue;exact:(linear0 (@exterior_differential_map R h2 n R^o m)).
Qed.
End CurrentClassOneExteriorCompact.
