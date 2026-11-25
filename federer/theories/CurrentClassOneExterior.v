(** Federer (1969), 4.1.7, p. 358:
    a class-one form has a continuous
    actual exterior derivative. This supporting
    consequence uses the original first-differential
    field and the proved bounded alternation
    map; no smoothness or compact support
    is added to the form. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormClassZeroPostcompose
  NormRegularity NormHigherDifferentialUP NormHigherDifferentialFirst
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed ContinuousMultilinearOne
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  ExteriorDerivativeUP CurrentCoefficientNorms CurrentExteriorDifferentialMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentClassOneExterior.
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
Local Notation L := (@current_exterior_differential_map R h2 n m).

(** Source for [current_class_one_exterior_continuous]:
    the original d phi of a
    class-one form is continuous on U,
    supporting the all-class-one boundary formula
    in Federer 4.1.7, p. 358.
    Its values satisfy the actual exterior
    derivative graph of 4.1.6, p. 352. *)
Theorem current_class_one_exterior_continuous (U:X->Prop) (phi:X->Y):
  norm_class hNX hNY U phi 1%N->
  exists beta:X->Z,norm_class_zero NX NZ U beta /\
    forall x,U x->has_exterior_derivative NX NY U phi x (beta x).
Proof.
move=>hClass.
have [_ [D [hActual hContinuous]]]:=hClass.
exists (fun x=>L (D x));split.
- exact:(@norm_class_zero_postcompose R X (J 1%N) Z NX (@JN 1%N) NZ
    (continuous_multilinear_norm_is_norm hNY (hJ 1%N)) U D L hContinuous
    (@current_exterior_differential_map_bounded R h2 n m)).
- move=>x hx.
  exists (@continuous_multilinear_one_operator R X Y (J 1%N) NX NY
    (@ej 1%N) (@JN 1%N) (hJ 1%N) (D x));split.
  + exact:((@norm_higher_differential_first R X Y NX NY hNX hNY J ej JN hJ
      U phi x (D x)).1 (hActual x hx)).
  + exact:current_exterior_differential_map_values.
Qed.
End CurrentClassOneExterior.
