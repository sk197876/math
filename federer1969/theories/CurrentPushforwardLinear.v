(** Federer (1969), 4.1.9, p. 363: the original
    homotopy identity uses linearity in the current
    of the support-proper pushforward from 4.1.7,
    p. 359. One actual compact cutoff gives
    the same source test for every term. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces
  CurrentEvaluation CurrentProperSupport CurrentSupportLinearUnion CurrentCommonPushforwardCutoff
  CurrentPushforwardSealed CurrentPushforwardCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPushforwardLinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation Proper := (fun T:C=>@is_current_proper_on_support R h2 n nu m U hU V T f hImage).
Local Notation push := (fun (T:C) (hp:Proper T)=>
  @CurrentPushforward.value R h2 n nu m U V hU hV T f hImage hf hp).
Local Notation source_action := (@current_value R h2 n U hU m).
Local Notation target_action := (@current_value R h2 nu V hV m).

(** Source for [current_pushforward_linear]: f#(cS+T)=
    c f#S+f#T on the original support-proper
    domain, supporting the current homotopy formula
    in Federer 4.1.9, p. 363. No measure,
    finite-mass or normal-current hypothesis is imposed. *)
Theorem current_pushforward_linear c (S T:C)
    (hS:Proper S) (hT:Proper T) (hCombination:Proper (c*:S+T)):
  push (c*:S+T) hCombination=c*:(push S hS)+push T hT.
Proof.
apply:(@current_values_extensional R h2 nu m V hV)=>phi.
have[gamma hPlateau]:=@current_common_pushforward_cutoff R h2 n nu m U V hU hV f hImage S T hS hT phi.
have hSValue:=@current_pushforward_original_cutoff_formula R h2 n nu m U V hU hV S f hImage hf
  hS phi gamma (fun x hx hPhi=>hPlateau x (or_introl hx) hPhi).
have hTValue:=@current_pushforward_original_cutoff_formula R h2 n nu m U V hU hV T f hImage hf
  hT phi gamma (fun x hx hPhi=>hPlateau x (or_intror hx) hPhi).
have hUnion:=@current_support_linear_union R h2 n m U hU c S T.
have hCombinationValue:=@current_pushforward_original_cutoff_formula R h2 n nu m U V hU hV
  (c*:S+T) f hImage hf hCombination phi gamma
  (fun x hx hPhi=>hPlateau x (hUnion x hx) hPhi).
rewrite hCombinationValue (linearP source_action) hom_addE hom_scaleE.
by rewrite (linearP target_action) hom_addE hom_scaleE hSValue hTValue.
Qed.
End CurrentPushforwardLinear.
