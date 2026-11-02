(** Federer (1969), 3.1.24, p. 239: analytic
    functions are closed under composition, with the printed
    quantitative derivative bound on the actual composite domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity NormRegularityOperations NormHigherDifferentialUP NormHigherSymmetricFormUP
  NormHigherSymmetricFormFamilies NormHigherDifferentialSymmetricForm NormHigherCompositionFormula
  SymmetricForms SymmetricOperatorNorm NormAnalyticUP NormSmoothFields NormAnalyticBoundNonnegative
  AnalyticCompositionCoefficientBound AnalyticCompositionScalarBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_at_composition]: composition
    preserves analyticity at a point, Federer 3.1.24,
    p. 239. Choose the intersection of the inner
    analytic neighbourhood with the inverse image of the outer
    one. The exact 3.1.11 composition formula, shuffle operator
    bound and scalar coefficient sum prove the constant
    c(gamma+1). No completeness is needed for this implication. *)
Theorem norm_analytic_at_composition (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    (A:set X) (B:set Y) (f:X->Y) (g:Y->T) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R Y T NY NT hNY hNT B g (f a) ->
  @norm_analytic_at R X T NX NT hNX hNT (fun x=>A x /\ B (f x)) (fun x=>g (f x)) a.
Proof.
move=>[U [c [ha [hUA [hf hbF]]]]] [V [d [hfa [hVB [hg hbG]]]]].
have hc:=norm_analytic_operator_witness_nonnegative ha hf hbF.
have hd:=norm_analytic_operator_witness_nonnegative hfa hg hbG.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ez i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
pose W i:=@ContinuousMultilinear.space R i Y T NY NT hNY hNT.
pose ew i:=@ContinuousMultilinear.evaluation R i Y T NY NT hNY hNT.
pose WN i:=@ContinuousMultilinear.norm R i Y T NY NT hNY hNT.
pose hW i:=@ContinuousMultilinear.laws R i Y T NY NT hNY hNT.
pose P i:=@ContinuousMultilinear.space R i X T NX NT hNX hNT.
pose ep i:=@ContinuousMultilinear.evaluation R i X T NX NT hNX hNT.
pose PN i:=@ContinuousMultilinear.norm R i X T NX NT hNX hNT.
pose hP i:=@ContinuousMultilinear.laws R i X T NX NT hNX hNT.
have [F hF]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY U f hf.
have [G hG]:=@norm_smooth_fields_exist R Y T NY NT hNY hNT V g hg.
pose C:=fun x=>U x /\ V (f x).
have hclass:norm_class_all_orders hNX hNT C (fun x=>g (f x)).
  move=>k; exact (@norm_class_composition R X Y T NX NY NT hNX hNY hNT U V f g k (hf k) (hg k)).
exists C,(c*(d+1)); split; first by split.
split; first by move=>x [hx hy]; split; [exact (hUA x hx)|exact (hVB (f x) hy)].
split; first exact hclass.
move=>p hp x hx z hz.
have [phi hphi]:=@norm_higher_differential_point_forms R X Y NX NY hNX hNY Z ez ZN hZ
  U f p x (fun i=>F i x) (fun i _=>(hF i).1 x hx.1).
have [psi hpsi]:=@norm_higher_differential_point_forms R Y T NY NT hNY hNT W ew WN hW
  V g p (f x) (fun i=>G i (f x)) (fun i _=>(hG i).1 (f x) hx.2).
have [eta [he hn]]:=@norm_higher_differential_symmetric_form_exists R p X T NX NT hNX hNT
  P ep PN hP C (fun y=>g (f y)) x z hz.
have hEta:is_norm_higher_differential_form NX ep PN C (fun y=>g (f y)) p x eta.
  exists z; split; first exact hz.
  move=>u; rewrite he; congr (@ep p _ z).
  by apply/ffunP=>j; rewrite ffunE tnth_mktuple.
have hpp:(1<=p<=p)%N by rewrite hp leqnn.
have hform:=@norm_higher_composition_formula R X Y T NX NY NT hNX hNY hNT
  Z W P ez ZN ew WN ep PN hZ hW hP U V f g p x phi psi hp hx.1 hx.2 (hf p) (hg p)
  (fun i hi=>(hphi i hi).1) (fun i hi=>(hpsi i hi).1) p hpp eta hEta.
have hphiB m (hm:(1<=m<=p)%N):
    (symmetric_operator_norm hNX.1 NY (phi m)<=(c^+m*(m`!)%:R)%:E)%E.
  rewrite (hphi m (andP hm).2).2 lee_fin.
  exact (hbF m (andP hm).1 x hx.1 (F m x) ((hF m).1 x hx.1)).
have hpsiB m (hm:(1<=m<=p)%N):
    (symmetric_operator_norm hNY.1 NT (psi m)<=(d^+m*(m`!)%:R)%:E)%E.
  rewrite (hpsi m (andP hm).2).2 lee_fin.
  exact (hbG m (andP hm).1 (f x) hx.2 (G m (f x)) ((hG m).1 (f x) hx.2)).
have hb:=@analytic_composition_form_operator_bound R X Y T NX NY NT hNX hNY hNT
  p phi psi c d hp hc hd hphiB hpsiB.
rewrite -hform hn lee_fin in hb.
have hs:=@analytic_composition_scalar_bound R c d p hc hd hp.
exact (le_trans hb (ler_wpM2r (ler0n R (p`!)) hs)).
Qed.

(** Source for [norm_analytic_composition]: the composition
    of two analytic functions is analytic, Federer 3.1.24,
    p. 239. Its actual domain consists precisely of
    inner-domain points whose images lie in the outer domain. *)
Theorem norm_analytic_composition (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    (A:set X) (B:set Y) (f:X->Y) (g:Y->T) :
  @norm_analytic R X Y NX NY hNX hNY A f ->
  @norm_analytic R Y T NY NT hNY hNT B g ->
  @norm_analytic R X T NX NT hNX hNT (fun x=>A x /\ B (f x)) (fun x=>g (f x)).
Proof.
move=>hf hg a [ha hb].
exact (@norm_analytic_at_composition R X Y T NX NY NT hNX hNY hNT A B f g a
  (hf a ha) (hg (f a) hb)).
Qed.
