(** Federer (1969), 4.1.27, p. 384:
    injectivity on the original cube leaves
    one nonzero term in the preceding
    full-fibre density of 4.1.25, p. 383.
    The other fibre points remain present;
    their actual defined coefficients are zero.
    Undefined summands retain the original partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing PairingLinear
  CurrentCoefficientNorms CurrentMultivectorDual MultivectorDualSealed ContinuousDualUP
  PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed
  NumericalSum NumericalSumSingleSupport CurrentAreaFibreSumUP
  CurrentAreaFibreSumEvaluations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_fibre_sum_single_support]: the original
    full-fibre sum equals its sole nonzero
    summand in the injective case of
    4.1.27, p. 384. No global
    injectivity, countability of the fibre or
    total definition of the input field
    is added to the preceding sum laws. *)
Theorem current_area_fibre_sum_single_support (R:realType)
    (h2:(1+1:R)!=0) (X:choiceType) n m
    (f:X->R_n R n)
    (u:partial_function X (exterior_power (R_n R n) m))
    y eta p w:
  @is_current_area_fibre_sum R X n m f u y eta->
  f p=y->partial_function_graph u p w->
  (forall x v,f x=y->x!=p->partial_function_graph u x v->v=0)->eta=w.
Proof.
move=>hSum hPoint hAt hOff.
pose r:=@PartialFunctionExtension.value X (exterior_power (R_n R n) m) u 0%R.
pose hR:=@PartialFunctionExtension.laws X (exterior_power (R_n R n) m) u 0%R.
have hOffR x:f x=y->x!=p->r x=0.
  move=>hF hDifferent.
  have[v hValue]:=@current_area_fibre_sum_input_domain R X n m f u y eta hSum x hF.
  by rewrite /r (hR x v hValue) (hOff x v hF hDifferent hValue).
have hAtR:r p=w:=hR p w hAt.
apply:(continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
apply:hom_ext=>a;rewrite !MultivectorDual.laws.
have hEvaluation:=@current_area_fibre_sum_extension_evaluations R X n m f u r y eta hR hSum a.
have hSingle:=@numerical_sum_single_support R X [set x|f x=y]
  (fun x=>(pairing (r x) a)%:E) p hPoint.
have hSumR:numerical_sum [set x|f x=y] (fun x=>(pairing (r x) a)%:E)=
    Some (pairing w a)%:E.
  rewrite -hAtR;apply:hSingle=>x hx hDifferent.
  rewrite (@hOffR x hx hDifferent).
  change ((pairing_left a 0)%:E=(0:R)%:E).
  by rewrite linear0.
have hBoth:=eq_trans (esym hEvaluation) hSumR.
by injection hBoth.
Qed.
