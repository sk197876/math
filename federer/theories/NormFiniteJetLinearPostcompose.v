(** Federer (1969), 3.4.5, pp. 318–321: finite
    actual jet agreement under bounded linear coefficient
    operations, supporting the actual derivative evaluations. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormAnalyticLinear
  NormOpenDomainLaws NormLittleOPower NormLittleODomination NormFiniteJetAgreement NormFiniteJetRadialRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_finite_jet_linear_postcompose]: applying
    a bounded linear map to two functions with the
    same actual finite jets preserves that agreement, supporting
    3.4.5, pp. 318–321. Actual analytic regularity
    and the proved linear norm bound discharge every premise. *)
Theorem norm_finite_jet_linear_postcompose (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    (A B:set X) (f g:X->Y) k a (L:Hom Y T):
  A a ->B a ->
  @norm_analytic R X Y NX NY hNX hNY A f ->
  @norm_analytic R X Y NX NY hNX hNY B g ->norm_bounded_linear NY NT L ->
  norm_finite_jet_agreement NX
    (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A B f g k a ->
  norm_finite_jet_agreement NX
    (fun i=>@ContinuousMultilinear.evaluation R i X T NX NT hNX hNT)
    (fun i=>@ContinuousMultilinear.norm R i X T NX NT hNX hNT)
    A B (fun x=>L (f x)) (fun x=>L (g x)) k a.
Proof.
move=>ha hb hf hg hL hAgree.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ez i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose NZ i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
pose W i:=@ContinuousMultilinear.space R i X T NX NT hNX hNT.
pose ew i:=@ContinuousMultilinear.evaluation R i X T NX NT hNX hNT.
pose NW i:=@ContinuousMultilinear.norm R i X T NX NT hNX hNT.
pose hW i:=@ContinuousMultilinear.laws R i X T NX NT hNX hNT.
have hLinear:=@norm_bounded_linear_analytic R Y T NY NT hNY hNT setT
  (fun y _=>norm_full_domain_interior NY y) L hL.
have hLF:=norm_analytic_compose_on (fun x (_:A x)=>Logic.I) hf hLinear.
have hLG:=norm_analytic_compose_on (fun x (_:B x)=>Logic.I) hg hLinear.
apply:(@norm_radial_remainder_finite_jet_agreement R X T NX NT hNX hNT W ew NW hW
  A B (fun x=>L (f x)) (fun x=>L (g x)) k a ha hb
  (norm_analytic_class_all_orders hLF k) (norm_analytic_class_all_orders hLG k))=>v.
have hRadial:=@norm_finite_jet_radial_remainder R X Y NX NY hNX hNY Z ez NZ hZ A B f g k a
  ha hb (norm_analytic_class_all_orders hf k) (norm_analytic_class_all_orders hg k) hAgree v.
have [C [hC hBound]]:=hL.
apply:(@norm_little_o_power_domination R Y T NY NT hNY
  (fun t=>f (a+t*:v)-g (a+t*:v)) (fun t=>L (f (a+t*:v))-L (g (a+t*:v))) k C 1 hC ltr01 _ hRadial).
move=>t _;rewrite -linearB;exact:hBound.
Qed.
