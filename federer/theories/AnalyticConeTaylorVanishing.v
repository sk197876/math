(** Federer (1969), 3.4.5, p. 321: actual
    homogeneous Taylor polynomials of a function vanishing
    on a real cone also vanish on that cone.
    This supports the example cited to Cartan (1957), pp. 97–99. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP NormClassOneUP NormRegularity NormRegularityOperations
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialSymmetricForm NormSmoothFields NormAnalyticUP NormAnalyticLocal
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm NormTaylorLineValues SmoothZeroRayJets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cone_taylor_polynomial_vanishing]:
    the original actual Taylor differential gives a
    symmetric form whose normalized diagonal vanishes on
    every original cone direction, supporting the example
    in 3.4.5, p. 321. The cone is only
    required to retain positive scalar multiples. *)
Theorem analytic_cone_taylor_polynomial_vanishing (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A C:set X) (f:X->R):
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A f ->
  A 0 ->
  (forall v,C v ->forall t:R,0<t ->C (t*:v)) ->
  (forall x,A x ->C x ->f x=0) ->
  forall m (z:@ContinuousMultilinear.space R m X R^o NX (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R)),
  has_norm_higher_differential NX
    (fun i=>@ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
    (fun i=>@ContinuousMultilinear.norm R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
    A f m 0 z ->
  exists phi:S_m X R^o m,
    (forall t,phi t=@ContinuousMultilinear.evaluation R m X R^o NX (fun t=>`|t|)
      hNX (@scalar_absolute_value_norm R) [ffun i=>tnth t i] z) /\
    forall v,C v ->sform_polynomial_value phi v=0.
Proof.
move=>hf hA hCone hZero m z hz.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
have hSmooth:=norm_analytic_class_all_orders hf.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX N hNX hN A f hSmooth.
have hContinuous:=norm_class_continuous (hSmooth 0%N).
have hEqual:z=D m 0:=norm_higher_differential_unique hNX hN hZ hz ((hD m).1 0 hA).
have [phi [hEvaluation hPhiNorm]]:=@norm_higher_differential_symmetric_form_exists R m X R^o
  NX N hNX hN Z ev NZ hZ A f 0 z hz.
exists phi;split;first exact:hEvaluation.
move=>v hV.
have [r0 [hr0 hBall]]:=(hContinuous 0 hA).1.
have [r [hr hSmall]]:=@norm_scalar_line_small_increments R X NX hNX v r0 hr0.
have hRay t (ht:0<t<r):f (t*:v)=0.
  have hNorm:`|t|<r by rewrite ger0_norm ?(ltW (andP ht).1) //;exact:(andP ht).2.
  have hMember:=hBall (t*:v) (hSmall t hNorm).
  rewrite add0r in hMember.
  exact:hZero _ hMember (hCone v hV t (andP ht).1).
have hJet:=@smooth_zero_ray_diagonal_jets R X NX hNX A f D v r hA hContinuous
  (fun i=>(hD i).1) (fun i=>(hD i).2) hr hRay m.
rewrite sform_polynomial_diagonal_value hEvaluation hEqual.
have hArguments:[ffun i:'I_m=>tnth [tuple v|_<m] i]=[ffun _:'I_m=>v].
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
by rewrite hArguments hJet scaler0.
Qed.
