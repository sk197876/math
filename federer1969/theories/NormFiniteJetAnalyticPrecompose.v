(** Federer (1969), 3.4.5, pp. 318–321: actual
    finite jets under analytic substitutions. This supporting
    consequence uses the uniform Taylor remainder and the
    first-order bound of 3.1.11, pp. 221–222. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticComposition
  NormClassOneUP NormClassOneLineGrowth NormLittleOPower NormLittleOPullback
  NormFiniteJetAgreement NormFiniteJetUniformRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_finite_jet_analytic_precompose]: equal
    actual finite jets stay equal after any actual analytic
    source substitution at the original centre, supporting
    3.4.5, pp. 318–321. All original preimage domains
    are retained, including finite order zero. *)
Theorem norm_finite_jet_analytic_precompose (R:realType) (V X Y:lmodType R)
    (NV:V->R) (NX:X->R) (NY:Y->R)
    (hNV:is_real_norm NV) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B:set X) (C:set V) (f g:X->Y) (t:V->X) k b:
  A (t b) ->B (t b) ->C b ->
  @norm_analytic R X Y NX NY hNX hNY A f ->
  @norm_analytic R X Y NX NY hNX hNY B g ->
  @norm_analytic R V X NV NX hNV hNX C t ->
  norm_finite_jet_agreement NX
    (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A B f g k (t b) ->
  norm_finite_jet_agreement NV
    (fun i=>@ContinuousMultilinear.evaluation R i V Y NV NY hNV hNY)
    (fun i=>@ContinuousMultilinear.norm R i V Y NV NY hNV hNY)
    (fun v=>C v /\A (t v)) (fun v=>C v /\B (t v)) (fun v=>f (t v)) (fun v=>g (t v)) k b.
Proof.
move=>ha hb hc hf hg ht hAgree.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ez i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose NZ i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
pose W i:=@ContinuousMultilinear.space R i V Y NV NY hNV hNY.
pose ew i:=@ContinuousMultilinear.evaluation R i V Y NV NY hNV hNY.
pose NW i:=@ContinuousMultilinear.norm R i V Y NV NY hNV hNY.
pose hW i:=@ContinuousMultilinear.laws R i V Y NV NY hNV hNY.
have hCompositeF:=norm_analytic_composition ht hf.
have hCompositeG:=norm_analytic_composition ht hg.
apply:(@norm_radial_remainder_finite_jet_agreement R V Y NV NY hNV hNY W ew NW hW
  (fun v=>C v /\A (t v)) (fun v=>C v /\B (t v)) (fun v=>f (t v)) (fun v=>g (t v)) k b
  (conj hc ha) (conj hc hb) (norm_analytic_class_all_orders hCompositeF k)
  (norm_analytic_class_all_orders hCompositeG k))=>v.
have ht1:=(@norm_class_firstP R V X NV NX hNV hNX C t).1
  (norm_analytic_class_all_orders ht 1%N).
have [L [r [hL [hr hBound]]]]:=norm_class_one_line_growth hNV hNX v hc ht1.
pose rho:=fun x:X=>f (t b+x)-g (t b+x).
have hUniform:=@norm_finite_jet_uniform_remainder R X Y NX NY hNX hNY Z ez NZ hZ
  A B f g k (t b) ha hb (norm_analytic_class_all_orders hf k)
  (norm_analytic_class_all_orders hg k) hAgree.
have hLittle:=norm_little_o_power_pullback hNX
  (rho:=rho) (v:=fun s=>t (b+s*:v)-t b) hL hr
  (fun s hs=>(hBound s hs).2) hUniform.
move=>epsilon hEpsilon;have [d [hd hEstimate]]:=hLittle epsilon hEpsilon.
exists d;split;first exact:hd.
move=>s hs;have:=hEstimate s hs.
by rewrite /rho ![t b+(_-t b)]addrC !subrK.
Qed.
