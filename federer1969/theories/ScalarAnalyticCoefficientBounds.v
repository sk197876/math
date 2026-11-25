(** Federer (1969), 3.1.24, p. 240: analyticity
    bounds the normalized scalar derivatives by powers of one
    finite positive constant, as required for the inverse majorant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearZero ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherSymmetricFormUP
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  NormAnalyticUP NormAnalyticDiagonal NormAnalyticNonnegative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_actual_zero_form_value]: the constant
    normalized derivative coefficient is f(a), supporting the
    inverse coefficient calculation in Federer 3.1.24, p. 240.
    This follows from the exact zeroth-differential graph,
    including its empty argument tuple. *)
Lemma scalar_actual_zero_form_value (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R) (A:R^o->Prop) (f:R^o->R^o) a (phi:S_m R^o R^o 0) :
  is_norm_higher_differential_form (fun t:R^o=>`|t|) ev ZN A f 0 a phi ->
  sform_polynomial_value phi 1= f a.
Proof.
move=>[z [hz he]].
pose u:{ffun 'I_0->R^o}:=[ffun i=>(1:R^o)].
have hEval:=he u.
have hTuple:[tuple u j | j<0]= [tuple (1:R^o) | i<0].
  apply:eq_from_tnth=>i; by have:=valP i; rewrite ltn0.
rewrite hTuple in hEval.
rewrite sform_polynomial_diagonal_value fact0 invr1 scale1r -hEval.
rewrite (zero_arity_arguments_unique u [ffun i:'I_0=>(0:R^o)]); exact hz.2.
Qed.

(** Source for [scalar_analytic_coefficients_exponential_bound]:
    the existence of a finite c with lambda_p<=c^p in
    Federer 3.1.24, p. 240. Analyticity bounds the
    absolute normalized scalar coefficients of actual derivative
    forms. Domain restrictions are transported through the
    exact graph laws. Strict positivity of c is obtained by
    increasing its nonnegative witness by one. *)
Theorem scalar_analytic_coefficients_exponential_bound (R:realType)
    (A:R^o->Prop) (f:R^o->R^o) a (phi:forall m,S_m R^o R^o m) :
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) A f a ->
  (forall m,is_norm_higher_differential_form (fun t:R^o=>`|t|)
    (fun j=>@ContinuousMultilinear.evaluation R j R^o R^o (fun t=>`|t|) (fun t=>`|t|)
      (scalar_absolute_value_norm R) (scalar_absolute_value_norm R))
    (fun j=>@ContinuousMultilinear.norm R j R^o R^o (fun t=>`|t|) (fun t=>`|t|)
      (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)) A f m a (phi m)) ->
  exists C:R,0<C /\ forall m,(1<=m)%N -> `|sform_polynomial_value (phi m) 1|<=C^+m.
Proof.
move=>hf hphi.
pose N:=fun t:R^o=>`|t|.
pose hN:=scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose ZN i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
have [U [c [ha [hUA [hc hb]]]]]:=@norm_analytic_diagonal R R^o R^o N N hN hN A f a hf.
have hcn:=norm_diagonal_witness_nonnegative ha hc hb.
have hC:0<c+1 by lra.
exists (c+1); split; first exact hC.
move=>m hm.
have [z [hz he]]:=hphi m.
have hOpen x (hx:U x):norm_domain_interior N U x:=((hc 0%N).1 x hx).1.
have hZU:=(@norm_higher_differential_open_restriction R R^o R^o N N hN hN Z ev ZN hZ
  m A U f hUA hOpen a ha z).1 hz.
have hunit:N (1:R^o)<=1 by rewrite /N normr1.
have hBound:=hb m hm a ha z hZU 1 hunit.
pose u:{ffun 'I_m->R^o}:=[ffun i=>(1:R^o)].
have hEval:=he u.
have hTuple:[tuple u j | j<m]= [tuple (1:R^o) | i<m].
  apply:eq_from_tnth=>i; by rewrite !tnth_mktuple /u ffunE.
rewrite hTuple in hEval.
rewrite sform_polynomial_diagonal_value -hEval.
apply:le_trans hBound _.
have hcc:c<=c+1 by rewrite lerDl ler01.
exact (lerXn2r m hcn (ltW hC) hcc).
Qed.
