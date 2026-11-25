(** Federer (1969), 3.2.33, p. 270: finite
    scalar polynomial operations in the actual exterior Gram
    rank tests h_i, using the analytic calculus of 3.1.24. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions ring.
From Federer Require Import RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticArithmetic NormAnalyticOperations
  NormAnalyticConstant ScalarPowerAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Products.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable A:set X.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN A f).

(** Source for [norm_analytic_scalar_power]: powers of
    analytic scalar functions in the Gram polynomials h_i,
    Federer 3.2.33, p. 270. Compose with the already
    proved scalar polynomial power; degree zero is retained. *)
Lemma norm_analytic_scalar_power (f:X->R) q:
  AN f ->AN (fun x=>(f x)^+q).
Proof.
move=>hf.
apply:(@norm_analytic_compose_on R X R^o R^o NX N N hNX hN hN
  A setT f (fun t=>t^+q) (fun x hx=>Logic.I) hf).
move=>t _; exact:(@scalar_power_analytic_at R q t).
Qed.

(** Source for [norm_analytic_scalar_product]: multiplication
    in the finite coordinate expression of h_i, Federer
    3.2.33, p. 270. The polarization identity reduces
    the product to analytic squares, addition and scalar
    multiplication; no product regularity is assumed. *)
Lemma norm_analytic_scalar_product (f g:X->R):
  AN f ->AN g ->AN (fun x=>f x*g x).
Proof.
move=>hf hg.
have hSum:=@norm_analytic_add R X R^o NX N hNX hN A f g hf hg.
have hSquare:=norm_analytic_scalar_power 2%N hSum.
have hF:=norm_analytic_scalar_power 2%N hf.
have hG:=norm_analytic_scalar_power 2%N hg.
have hDifference:=@norm_analytic_subtract R X R^o NX N hNX hN A
  (fun x=>(f x+g x)^+2-(f x)^+2) (fun x=>(g x)^+2)
  (@norm_analytic_subtract R X R^o NX N hNX hN A
    (fun x=>(f x+g x)^+2) (fun x=>(f x)^+2) hSquare hF) hG.
have hScaled:AN (fun x=>(1/2:R)*:(((f x+g x)^+2-(f x)^+2-(g x)^+2):R^o)).
  move=>a ha; exact:(@norm_analytic_at_scale R X R^o NX N hNX hN A
    (fun x=>(f x+g x)^+2-(f x)^+2-(g x)^+2) a (1/2) (hDifference a ha)).
apply:(@norm_analytic_domain_agreement R X R^o NX N hNX hN A
  (fun x=>(1/2:R)*:(((f x+g x)^+2-(f x)^+2-(g x)^+2):R^o)) (fun x=>f x*g x) _ hScaled)=>x hx.
change ((1/2:R)*((f x+g x)^+2-(f x)^+2-(g x)^+2)=f x*g x).
have hTwo:(2:R)!=0 by rewrite pnatr_eq0.
by rewrite !expr2; field.
Qed.

(** Source for [norm_analytic_finite_scalar_sum]: finite
    Gram and determinant sums in Federer 3.2.33,
    p. 270, are analytic. The explicit open-domain
    hypothesis covers the empty scalar family as well. *)
Lemma norm_analytic_finite_scalar_sum (I:finType) (f:I->X->R):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,AN (f i)) ->AN (fun x=>\sum_i f i x).
Proof.
move=>hOpen hf.
have hSum:AN (\sum_i f i).
  elim/big_ind:_=>[|g h hg hh|i _].
  - exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen 0).
  - exact:(norm_analytic_add hg hh).
  - exact:hf.
apply:(@norm_analytic_domain_agreement R X R^o NX N hNX hN A
  (\sum_i f i) (fun x=>\sum_i f i x) _ hSum)=>x hx.
by elim/big_rec2:_=>[|i y F _ <-].
Qed.

(** Source for [norm_analytic_finite_scalar_product]: the
    finite products in the coordinate determinant formula for
    h_i, Federer 3.2.33, p. 270, are analytic.
    The empty product is the actual constant one, as
    needed in exterior degree zero. *)
Lemma norm_analytic_finite_scalar_product (I:finType) (f:I->X->R):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,AN (f i)) ->AN (fun x=>\prod_i f i x).
Proof.
move=>hOpen hf.
have hProduct:AN (\prod_i f i).
  elim/big_ind:_=>[|g h hg hh|i _].
  - exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen 1).
  - exact:(norm_analytic_scalar_product hg hh).
  - exact:hf.
apply:(@norm_analytic_domain_agreement R X R^o NX N hNX hN A
  (\prod_i f i) (fun x=>\prod_i f i x) _ hProduct)=>x hx.
by elim/big_rec2:_=>[|i y F _ <-].
Qed.
End Products.
