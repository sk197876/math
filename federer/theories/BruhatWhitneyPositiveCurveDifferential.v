(** Federer (1969), 3.4.10, p. 338:
    the two actual curves on the cited surface
    have derivatives (s,1,b). Assemble their checked
    scalar differentials by the existing coordinate synthesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology ring.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP NormDifferentialLinear
  NormDifferentialLocal NormDifferentialFiniteSynthesis NormAffineDilationDifferentials
  NormHigherCurveDerivativeUP EuclideanCoordinateTopology FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness
  BruhatWhitneyPositiveCurves BruhatWhitneyPositiveHeightDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_positive_curve_differential]:
    the actual differential at the original axis point,
    supporting the nonregularity example cited in 3.4.10,
    p. 338. The discriminant domain is retained. *)
Theorem bruhat_whitney_positive_curve_differential (R:realType) (b s:R):
  let X:=R_n R 3 in
  let N:=fun t:R^o=>`|t| in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let j:=Ordinal (isT:(1<3)%N) in
  exists L:Hom R^o X,
    has_norm_differential N NX [set t|0<1+4*t]
      (@bruhat_whitney_positive_curve R b s) 0 L /\
    forall t,L t=t*:([ffun i=>if i==ord0 then s else if i==j then 1 else b]:X).
Proof.
move=>X N NX j.
pose hN:=@scalar_absolute_value_norm R.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3).
pose A:set R^o:=[set t|0<1+4*t].
have hHeight:=@bruhat_whitney_positive_height_differential R b.
have hInterior:=norm_differential_interior hHeight.
have hLinear c:has_norm_differential N N A (fun t:R^o=>c*t) 0
    (@scalar_coefficient_linear_map R R^o c).
  have hOriginal:=@norm_affine_dilation_differential R R^o N hN c 0 0.
  have hMap:c*:hom_of_linear (linear_id R^o)=@scalar_coefficient_linear_map R R^o c.
    apply:hom_ext=>t;change (c*t=t*c);exact:mulrC.
  rewrite hMap in hOriginal.
  have hRestricted:=@norm_differential_restrict R R^o R^o N N
    setT A (fun t=>c*:t+0) 0 (@scalar_coefficient_linear_map R R^o c)
    (fun _ _=>Logic.I) hInterior hOriginal.
  apply:(norm_differential_domain_agreement hN _ hRestricted)=>t _.
  change (c*t+0=c*t);exact:addr0.
pose F:=fun (i:'I_3) (t:R^o)=>if i==ord0 then s*t
  else if i==j then t else b*(1+Num.sqrt (1+4*t))/2.
pose C:=fun i:'I_3=>if i==ord0 then s else if i==j then 1 else b.
pose D:=fun i:'I_3=>@scalar_coefficient_linear_map R R^o (C i).
have hEach i:has_norm_differential N N A (F i) 0 (D i).
  rewrite /F /D /C;case:(i==ord0);first exact:hLinear s.
  case:(i==j);last exact:hHeight.
  apply:(norm_differential_domain_agreement hN _ (hLinear 1))=>t _;exact:mul1r.
have [L [hL hValue]]:=@norm_differential_finite_synthesis R R^o X N NX hN hNX
  A 0 [the finType of 'I_3] (@coordinate_basis R 3) F D hInterior hEach.
exists L;split.
- apply:(norm_differential_domain_agreement hN _ hL)=>t _.
  have hExpand:=@euclidean_coordinate_expansion R 3
    (@bruhat_whitney_positive_curve R b s t).
  have hEqual:(\sum_i @bruhat_whitney_positive_curve R b s t i*:
      @coordinate_basis R 3 i)=\sum_i F i t*:@coordinate_basis R 3 i.
    by apply:eq_bigr=>i _;rewrite /bruhat_whitney_positive_curve ffunE.
  by move:hExpand;rewrite hEqual.
- move=>t;rewrite hValue.
  change ((\sum_i (t*C i)*:@coordinate_basis R 3 i)=
    t*:([ffun i=>C i]:X)).
  have hExpand:=@euclidean_coordinate_expansion R 3 [ffun i=>C i].
  have hEqual:(\sum_i [ffun j=>C j] i*:@coordinate_basis R 3 i)=
      \sum_i C i*:@coordinate_basis R 3 i.
    by apply:eq_bigr=>i _;rewrite ffunE.
  rewrite hEqual in hExpand;rewrite -hExpand scaler_sumr.
  apply:eq_bigr=>i _;by rewrite scalerA.
Qed.
