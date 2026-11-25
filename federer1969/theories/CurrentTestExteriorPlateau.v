(** Federer (1969), 4.1.7, pp. 358–359:
    the original differential of a scalar
    cutoff vanishes on its plateau. This
    supporting locality law uses only the
    genuine first differential from Chapter 3. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLinear
  NormDifferentialDirectional NormDifferentialLocalAgreement NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentSpaces CurrentTestExteriorDerivative
  ExteriorDifferentialUP ExteriorDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTestExteriorPlateau.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o 0).
Local Notation NY := (@current_form_comass R h2 n 0%N).
Local Notation hNY := (@current_form_comass_real_norm R h2 n 0%N).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation value := (@current_test_value R h2 n U hU 0%N).

(** Source for [current_test_exterior_plateau_zero]:
    d gamma vanishes on every original
    open region where gamma is constant,
    supporting cutoff independence and the
    support obstruction in Federer 4.1.7,
    pp. 358–359. *)
Theorem current_test_exterior_plateau_zero gamma (W:set X) c:
  @open (real_norm_metric_space hNX) W->W `<=` U->
  (forall x,W x->value gamma x=c) ->forall x,W x->
    @current_test_value R h2 n U hU 1%N
      (@current_test_exterior_derivative R h2 n 0%N U hU gamma) x=0.
Proof.
move=>hW hWU hConstant x hx.
have hInterior:norm_domain_interior NX W x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  rewrite openE in hW;exact:hW x hx.
have [r [hr hInside]]:=hInterior.
have hConst:=@norm_differential_constant R X Y NX NY hNX hNY U x c (hU x (hWU x hx)).
have hZero:has_norm_differential NX NY U (value gamma) x 0.
  apply:(@norm_differential_local_agreement R X Y NX NY hNX U U (fun _=>c)
    (value gamma) x 0 r hr (fun h hh=>iff_refl _) _ hConst)=>h hh _.
  exact:esym (hConstant (x+h) (hInside h hh)).
have [L [hL hD]]:=@current_test_exterior_derivative_actual R h2 n 0%N U hU gamma x (hWU x hx).
have hSame:=norm_differential_unique hNX hNY hL hZero.
rewrite hSame in hD.
have hValue:=exterior_differential_value_unique hD (@ExteriorDifferential.laws R h2 n R^o 0%N 0).
rewrite hValue.
exact:(linear0 (@exterior_differential_map R h2 n R^o 0%N)).
Qed.
End CurrentTestExteriorPlateau.
