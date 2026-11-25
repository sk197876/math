(** Federer (1969), 3.1.24, pp. 240–241: choose
    actual symmetric Taylor forms with their analytic norm bounds,
    before converting them to coordinate partial derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormClassOneUP NormRegularity NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherSymmetricFormUP NormHigherDifferentialSymmetricForm SymmetricForms
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm SymmetricOperatorNorm
  NormAnalyticUP NormAnalyticDiagonal NormAnalyticTaylor NormAnalyticBoundNonnegative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_bounded_taylor_forms]: supporting
    the coordinate expansion in Federer 3.1.24, pp. 240–241.
    An analytic map has a uniform Taylor expansion near a
    whose coefficient forms are the actual differentials on
    the original domain and retain the bounds c^m m! in
    positive degree. The constant form is unrestricted. *)
Theorem norm_analytic_bounded_taylor_forms (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  exists (U:set X) (c:R) (phi:forall m,S_m X Y m),
    0<=c /\ U a /\ U `<=` A /\
    (forall x,U x -> norm_domain_interior NX U x) /\
    (forall m,is_norm_higher_differential_form NX
      (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
      (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A f m a (phi m)) /\
    (forall m,(1<=m)%N -> (symmetric_operator_norm hNX.1 NY (phi m)<=(c^+m*(m`!)%:R)%:E)%E) /\
    forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N -> forall x,U x ->
      NY (f x-\sum_(m<N.+1) sform_polynomial_value (phi m) (x-a))<eps.
Proof.
move=>[V [c [ha [hVA [hclass hb]]]]].
have hc:=norm_analytic_operator_witness_nonnegative ha hclass hb.
have hAnalV:@norm_analytic_at R X Y NX NY hNX hNY V f a.
  exists V,c; split; first exact ha.
  split; first by move=>x hx.
  by split.
have ht:=@norm_diagonal_analytic_taylor R X Y NX NY hNX hNY V f a
  (@norm_analytic_diagonal R X Y NX NY hNX hNY V f a hAnalV).
move:ht=>[U [hUa [hUV [hUclass [D [hD hlim]]]]]].
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hUclass 0%N).1 x hx).1.
have hex m:=@norm_higher_differential_symmetric_form_exists R m X Y NX NY hNX hNY
  Z ev ZN hZ U f a (D m) (hD m).
pose phi m:=projT1 (cid (hex m)).
have hphi m:=projT2 (cid (hex m)).
have hActual m:is_norm_higher_differential_form NX ev ZN A f m a (phi m).
  exists (D m); split.
  - exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
      m A U f (fun x hx=>hVA x (hUV x hx)) hOpen a hUa (D m)).2 (hD m)).
  - move=>u; rewrite (hphi m).1.
    congr (ev m _ (D m)); apply/ffunP=>j; by rewrite ffunE tnth_mktuple.
have hNorm m (hm:(1<=m)%N):
    (symmetric_operator_norm hNX.1 NY (phi m)<=(c^+m*(m`!)%:R)%:E)%E.
  rewrite (hphi m).2 lee_fin.
  apply:(hb m hm a).
  - exact (hUV a hUa).
  - exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
      m V U f hUV hOpen a hUa (D m)).2 (hD m)).
exists U,c,phi; split; first exact hc.
split; first exact hUa.
split; first by move=>x hx; exact (hVA x (hUV x hx)).
split; first exact hOpen.
split; first exact hActual.
split; first exact hNorm.
move=>eps heps; have [k hk]:=hlim eps heps.
exists k=>N hN x hx.
have he: (\sum_(m<N.+1) (m`!)%:R^-1 *: ev m [ffun i=>x-a] (D m))=
    \sum_(m<N.+1) sform_polynomial_value (phi m) (x-a).
  apply:eq_bigr=>m _; rewrite sform_polynomial_diagonal_value (hphi m).1.
  congr (_*:ev m _ (D m)); apply/ffunP=>j; by rewrite !ffunE tnth_mktuple.
by rewrite -he; exact (hk N hN x hx).
Qed.
