(** Federer (1969), 3.4.5, pp. 318–321: actual
    two-direction divided coefficient products, supporting the
    finite axis remainder proof of the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticLocal
  NormAnalyticScalarProducts AnalyticDirectionalCoefficient AnalyticDirectionalCoefficientAgreement
  AnalyticDirectionalCoefficientArithmetic AnalyticDirectionalCoefficientLocal AnalyticDirectionalCoefficientProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IteratedProduct.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation AN A f:=(@norm_analytic R X R^o NX N hNX hN A f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).

(** Source for [analytic_iterated_coefficient_product]: two
    actual divided directional coefficient operations turn a
    product into the finite two-index convolution, supporting
    3.4.5, pp. 318–321. All fields satisfy
    original recursive derivative equations; no formal series
    or coefficient product rule is assumed. *)
Theorem analytic_iterated_coefficient_product (A:set X) (f g:X->R) v w a
    (C D:nat->X->R) (P Q:nat->nat->X->R) i j (E H:X->R):
  A a ->AN A f ->AN A g ->
  (forall r,Coefficient A f r v (C r)) ->(forall r,Coefficient A g r v (D r)) ->
  (forall r s,Coefficient A (C r) s w (P r s)) ->
  (forall r s,Coefficient A (D r) s w (Q r s)) ->
  Coefficient A (fun x=>f x*g x) i v E ->Coefficient A E j w H ->
  H a=\sum_(r<i.+1) \sum_(s<j.+1) P (i-r)%N (j-s)%N a*Q r s a.
Proof.
move=>ha hf hg hC hD hP hQ hE hH.
have hOpen x (hx:A x):norm_domain_interior NX A x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have hAnalyticC r:AN A (C r):=@analytic_directional_coefficient_analytic R X R^o NX N hNX hN
  A f r v (C r) hf (hC r).
have hAnalyticD r:AN A (D r):=@analytic_directional_coefficient_analytic R X R^o NX N hNX hN
  A g r v (D r) hg (hD r).
pose B:=fun (r:'I_i.+1) x=>C (i-r)%N x*D r x.
have hB r:AN A (B r):=norm_analytic_scalar_product (hAnalyticC (i-r)%N) (hAnalyticD r).
have hEach (r:'I_i.+1):exists K:X->R,Coefficient A (B r) j w K /\AN A K.
  exact:(@analytic_directional_coefficient_exists R X R^o NX N hNX hN A (B r) j w (hB r)).
have [K hK]:=choice hEach.
pose T:=fun x:X=>\sum_(r<i.+1) B r x.
pose S:=fun x:X=>\sum_(r<i.+1) K r x.
have hT:AN A T:=norm_analytic_finite_scalar_sum hOpen hB.
have hS:Coefficient A T j w S:=@analytic_directional_coefficient_finite_sum R X R^o NX N hNX hN
  A (Finite.clone 'I_i.+1 _) B j w K hOpen hB (fun r=>(hK r).1).
have hValue x (hx:A x):E x=T x.
  exact:(@analytic_directional_coefficient_product R X NX hNX A f g i v x C D E hx hf hg
    (fun r _=>hC r) (fun r _=>hD r) hE).
have hHT:Coefficient A T j w H:=@analytic_directional_coefficient_domain_agreement R X R^o NX N hNX hN
  A E T j w H hOpen hValue hH.
have hPoint:H a=S a:=@analytic_directional_coefficient_unique R X R^o NX N hNX hN
  A T j w H S hT hHT hS a ha.
rewrite hPoint /S;apply:eq_bigr=>r _.
exact:(@analytic_directional_coefficient_product R X NX hNX A (C (i-r)%N) (D r) j w a
  (P (i-r)%N) (Q r) (K r) ha (hAnalyticC (i-r)%N) (hAnalyticD r)
  (fun s _=>hP (i-r)%N s) (fun s _=>hQ r s) (hK r).1).
Qed.
End IteratedProduct.
