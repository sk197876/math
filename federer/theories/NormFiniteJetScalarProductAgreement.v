(** Federer (1969), 3.4.5, pp. 318–321: multiplying
    by an actual analytic coefficient preserves finite jet
    agreement, supporting the cleared axis remainders. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticScalarProducts
  NormJetLineRemainder NormLittleOPower NormLittleODomination NormFiniteJetAgreement NormFiniteJetRadialRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Products.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X R^o NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X R^o NX N hNX hN).
Local Notation AN A f:=(@norm_analytic R X R^o NX N hNX hN A f).

(** Source for [norm_finite_jet_analytic_scalar_factor]:
    an actual analytic common scalar factor preserves every
    original finite agreeing jet, supporting 3.4.5,
    pp. 318–321. Its needed local bound follows
    from actual continuity, without a boundedness hypothesis. *)
Theorem norm_finite_jet_analytic_scalar_factor (A:set X) (f g h:X->R) k a:
  A a ->AN A f ->AN A g ->AN A h ->
  norm_finite_jet_agreement NX ev NZ A A f g k a ->
  norm_finite_jet_agreement NX ev NZ A A (fun x=>f x*h x) (fun x=>g x*h x) k a.
Proof.
move=>ha hf hg hh hAgree.
have hFH:=norm_analytic_scalar_product hf hh.
have hGH:=norm_analytic_scalar_product hg hh.
apply:(@norm_radial_remainder_finite_jet_agreement R X R^o NX N hNX hN Z ev NZ hZ A A
  (fun x=>f x*h x) (fun x=>g x*h x) k a ha ha
  (norm_analytic_class_all_orders hFH k) (norm_analytic_class_all_orders hGH k))=>v.
have hRadial:=@norm_finite_jet_radial_remainder R X R^o NX N hNX hN Z ev NZ hZ A A f g k a
  ha ha (norm_analytic_class_all_orders hf k) (norm_analytic_class_all_orders hg k) hAgree v.
have [M [r [hM [hr hBound]]]]:=norm_class_zero_line_bounded hNX hN v ha
  (norm_class_continuous (norm_analytic_class_all_orders hh 0%N)).
apply:(@norm_little_o_power_domination R R^o R^o N N hN
  (fun t=>f (a+t*:v)-g (a+t*:v))
  (fun t=>f (a+t*:v)*h (a+t*:v)-g (a+t*:v)*h (a+t*:v)) k M r hM hr _ hRadial).
move=>t /andP [_ ht];rewrite /N -mulrBl normrM mulrC.
exact:(ler_wpM2r (normr_ge0 _) (hBound t ht).2).
Qed.
End Products.
