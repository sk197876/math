(** Federer (1969), 3.1.24, p. 239: identify
    the actual scalar composite derivative before evaluating
    the abstract higher-composition formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import TensorUP Hom Bilinear RealNormUP ContinuousMultilinearUP
  SymmetricForms SymmetricFunctionalProduct NormDifferentialUP NormHigherSymmetricFormUP NormHigherDifferentialUP
  NormHigherDifferentialArithmetic NormHigherDifferentialLocal NormHigherDifferentialUnique NormClassZeroComposition
  ScalarAnalyticFraction ScalarAnalyticFractionDifferentials ScalarAnalyticFractionForms ScalarAnalyticFractionComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_analytic_composition_form_actual]: the
    derivative of (g composed with f)(x)=gamma x/[1-(gamma+1)x]
    for f(x)=x/(1-x), g(y)=gamma y/(1-gamma y),
    in Federer 3.1.24, p. 239. Its actual pth
    form at zero is gamma/(gamma+1) times the pth
    form of the rational function with parameter gamma+1.
    Both original domains are retained and every comparison
    with the simplified expression is justified on their intersection. *)
Theorem scalar_analytic_composition_form_actual (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun x:R^o=>`|x|) (fun x:R^o=>`|x|)
      (@ev i) (@ZN i)) (g:R) p :
  0<=g -> (1<=p)%N ->
  is_norm_higher_differential_form (fun x:R^o=>`|x|) ev ZN
    (fun x=>scalar_analytic_fraction_domain 1 x /\
      scalar_analytic_fraction_domain g (scalar_analytic_fraction 1 x))
    (fun x=>scalar_analytic_fraction g (scalar_analytic_fraction 1 x)) p 0
    ((g/(g+1))*:scalar_analytic_fraction_form (g+1) p).
Proof.
move=>hg hp.
pose N:=fun x:R^o=>`|x|.
have hN:=scalar_absolute_value_norm R.
pose C:=fun x=>scalar_analytic_fraction_domain 1 x /\
  scalar_analytic_fraction_domain g (scalar_analytic_fraction 1 x).
pose B:=scalar_analytic_fraction_domain (g+1).
pose t:=g/(g+1).
have hgp:0<g+1 by lra.
have hgne:g+1!=0:=lt0r_neq0 hgp.
have [hf _]:=scalar_analytic_fraction_differentials hZ (1:R).
have [hgReg _]:=scalar_analytic_fraction_differentials hZ g.
have [hH [D [hD heD]]]:=scalar_analytic_fraction_differentials hZ (g+1).
have hcomp:=norm_class_zero_composition (hf 0%N).1 (hgReg 0%N).1.
have hopen x (hx:C x):norm_domain_interior N C x:= (hcomp x hx).1.
have hCB x (hx:C x):B x.
  have hh:=scalar_analytic_fraction_composition_domain hx.1 hx.2.
  by rewrite mul1r in hh.
have hC0:C 0.
  split; first exact: scalar_analytic_fraction_zero_domain.
  rewrite scalar_analytic_fraction_zero; exact: scalar_analytic_fraction_zero_domain.
have hscaled x (hx:B x):has_norm_higher_differential N ev ZN B
    (fun y=>t*scalar_analytic_fraction (g+1) y) p x (t*:D p x).
  exact (@norm_higher_differential_field_scale R R^o R^o N N hN hN Z ev ZN hZ B p
    (scalar_analytic_fraction (g+1)) (D p) t (hD p) x hx).
have hrestrict:has_norm_higher_differential N ev ZN C
    (fun y=>t*scalar_analytic_fraction (g+1) y) p 0 (t*:D p 0).
  exact ((@norm_higher_differential_open_restriction R R^o R^o N N hN hN Z ev ZN hZ
    p B C (fun y=>t*scalar_analytic_fraction (g+1) y) hCB hopen 0 hC0 (t*:D p 0)).1
    (hscaled 0 (hCB 0 hC0))).
have hfg x (hx:C x) (_:C x):t*scalar_analytic_fraction (g+1) x=
    scalar_analytic_fraction g (scalar_analytic_fraction 1 x).
  have hh:=scalar_analytic_fraction_composition_value hgne hx.1 hx.2.
  by rewrite mul1r in hh; symmetry.
have hactual:has_norm_higher_differential N ev ZN C
    (fun x=>scalar_analytic_fraction g (scalar_analytic_fraction 1 x)) p 0 (t*:D p 0).
  exact ((@norm_higher_differential_local_agreement R R^o R^o N N hN hN Z ev ZN hZ
    p C C C (fun y=>t*scalar_analytic_fraction (g+1) y)
    (fun x=>scalar_analytic_fraction g (scalar_analytic_fraction 1 x))
    hopen (fun x _=>iff_refl (C x)) hfg 0 hC0 (t*:D p 0)).1 hrestrict).
exists (t*:D p 0); split; first exact hactual.
have [z [hz he]]:=scalar_analytic_fraction_form_actual hZ (g+1) p.
have hEq:D p 0= z:=@norm_higher_differential_unique R R^o R^o N N hN hN Z ev ZN hZ
  B (scalar_analytic_fraction (g+1)) p 0 (D p 0) z (hD p 0 (hCB 0 hC0)) hz.
move=>u; by rewrite (linZ (hom_linear (@ev p u))) sform_scaleE hEq (he u).
Qed.
