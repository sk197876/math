(** Federer (1969), 4.1.7, p. 359:
    a compact test agreeing with
    a smooth form near a
    support has the same exterior
    derivative there. This supporting locality
    law reuses the actual first
    differential from 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional
  NormDifferentialLocalAgreement NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentTestExteriorDerivative SmoothCurrentExteriorDerivative ExteriorDerivativeUP ExteriorDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTestExteriorAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation next := (@current_test_value R h2 n U hU m.+1).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation fv := (@current_smooth_value R h2 n U hU m.+1).
Local Notation td := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation sd := (@smooth_current_exterior_derivative R h2 n m U hU).

(** Source for [current_test_exterior_local_agreement]:
    actual test and smooth exterior
    derivatives agree on every original
    open agreement neighbourhood, supporting boundary
    commutation in Federer 4.1.7, p. 359.
    No equality outside that neighbourhood
    is required of the forms. *)
Theorem current_test_exterior_local_agreement (psi:DT) (phi:E) (W:set X):
  @open (real_norm_metric_space hNX) W->W `<=` U->
  (forall x,W x->value psi x=ev phi x)->
  forall x,W x->next (td psi) x=fv (sd phi) x.
Proof.
move=>hW hWU hAgreement x hx.
have [r [hr hInside]]:=(@norm_domain_interior_neighbourhood R X NX hNX W x).2
  (open_nbhs_nbhs (conj hW hx)).
have [M [hM hExteriorM]]:=@smooth_current_exterior_derivative_actual R h2 n m U hU phi x (hWU x hx).
have hPsi:has_norm_differential NX NY U (value psi) x M.
  apply:(@norm_differential_local_agreement R X Y NX NY hNX U U (ev phi) (value psi)
    x M r hr (fun h hh=>iff_refl _) _ hM)=>h hh hu.
  exact:esym (hAgreement (x+h) (hInside h hh)).
have [L [hL hExteriorL]]:=@current_test_exterior_derivative_actual R h2 n m U hU psi x (hWU x hx).
have hSame:=norm_differential_unique hNX hNY hL hPsi.
rewrite hSame in hExteriorL;exact:exterior_differential_value_unique hExteriorL hExteriorM.
Qed.
End CurrentTestExteriorAgreement.
