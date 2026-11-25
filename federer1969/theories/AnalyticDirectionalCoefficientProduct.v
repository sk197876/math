(** Federer (1969), 3.4.5, pp. 318–321: actual
    divided Taylor coefficient products, supporting the finite
    axis remainder calculation in the cited example. This is
    the original Leibniz rule of 3.1.11, p. 222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import TensorUP Hom ScalarCoefficients BoundedHom HomogeneousHom Bilinear RealNormUP
  SymmetricForms SymmetricFormSum HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  SymmetricFormProduct SymmetricPolynomialEvaluation SymmetricPolynomialProduct
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherSymmetricFormUP
  NormHigherSymmetricFormFamilies NormHigherDifferentialSymmetricForm NormHigherLeibniz
  NormAnalyticUP NormAnalyticLocal NormAnalyticScalarProducts NormSmoothFields
  AnalyticDirectionalCoefficient AnalyticDirectionalCoefficientForm.
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
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).

(** Source for [analytic_directional_coefficient_product]: the
    divided directional coefficient of an actual analytic product
    is the convolution of its actual divided coefficient
    fields, supporting 3.4.5, pp. 318–321. Factorial
    normalization cancels the original shuffle coefficient exactly. *)
Theorem analytic_directional_coefficient_product (A:set X) (f g:X->R) k v a
    (F G:nat->X->R) (c:X->R):
  A a ->AN A f ->AN A g ->
  (forall i,(i<=k)%N ->Coefficient A f i v (F i)) ->
  (forall i,(i<=k)%N ->Coefficient A g i v (G i)) ->
  Coefficient A (fun x=>f x*g x) k v c ->
  c a=\sum_(j<k.+1) F (k-j)%N a*G j a.
Proof.
move=>ha hf hg hCF hCG hc.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX N hNX hN A f (norm_analytic_class_all_orders hf).
have [E hE]:=@norm_smooth_fields_exist R X R^o NX N hNX hN A g (norm_analytic_class_all_orders hg).
have [phi hPhi]:=@norm_higher_differential_point_forms R X R^o NX N hNX hN Z ev NZ hZ
  A f k a (fun i=>D i a) (fun i _=>(hD i).1 a ha).
have [psi hPsi]:=@norm_higher_differential_point_forms R X R^o NX N hNX hN Z ev NZ hZ
  A g k a (fun i=>E i a) (fun i _=>(hE i).1 a ha).
have hProduct:=norm_analytic_scalar_product hf hg.
have [H hH]:=@norm_smooth_fields_exist R X R^o NX N hNX hN A (fun x=>f x*g x)
  (norm_analytic_class_all_orders hProduct).
have [eta [hEta hEtaNorm]]:=@norm_higher_differential_symmetric_form_exists R k X R^o NX N hNX hN
  Z ev NZ hZ A (fun x=>f x*g x) a (H k a) ((hH k).1 a ha).
have hActualEta:is_norm_higher_differential_form NX ev NZ A (fun x=>f x*g x) k a eta.
  exists (H k a);split;first exact:(hH k).1 a ha.
  move=>u;rewrite hEta;congr (ev k _ (H k a)).
  by apply/ffunP=>i;rewrite ffunE tnth_mktuple.
have hMul x y:N (x*y)<=N x*N y by rewrite /N normrM.
have hLeibniz:=@norm_higher_leibniz R X R^o NX N hNX hN Z ev NZ hZ (fun x y:R^o=>x*y)
  (@scalar_bilinear R) hMul A f g k a phi psi ha (norm_analytic_class_all_orders hf k)
  (norm_analytic_class_all_orders hg k) (fun i hi=>(hPhi i hi).1) (fun i hi=>(hPsi i hi).1)
  k (leqnn k) eta hActualEta.
have hEvalLinear:linear (fun S:S_star X R^o=>symmetric_polynomial_value S v).
  move=>b S T;exact:(congr1 (fun u:X->R^o=>u v)
    (@symmetric_polynomial_value_linear R X R^o b S T)).
pose Eval:Hom (S_star X R^o) R^o:=@HomMap R (S_star X R^o) R^o
  (fun S=>symmetric_polynomial_value S v) (introT (asboolP _) hEvalLinear).
have hEvaluated:=congr1 Eval hLeibniz.
rewrite linear_sum /Eval /= symmetric_polynomial_value_include in hEvaluated.
have hSum:(\sum_(j<k.+1) symmetric_polynomial_value
    (symmetric_forms_product (@scalar_bilinear R) (sform_include (phi (k-j)%N)) (sform_include (psi j))) v)=
    \sum_(j<k.+1) sform_polynomial_value (phi (k-j)%N) v*sform_polynomial_value (psi j) v.
  apply:eq_bigr=>j _;by rewrite (symmetric_polynomial_product_value (@pchar_num R))
    !symmetric_polynomial_value_include.
rewrite hSum in hEvaluated.
rewrite (analytic_directional_coefficient_form_value ha hc hActualEta) hEvaluated.
apply:eq_bigr=>j _.
have hJ:(j<=k)%N by have:=ltn_ord j;rewrite ltnS.
have hKJ:(k-j<=k)%N:=leq_subr j k.
rewrite (analytic_directional_coefficient_form_value ha (hCF _ hKJ) (hPhi _ hKJ).1)
  (analytic_directional_coefficient_form_value ha (hCG _ hJ) (hPsi _ hJ).1).
by [].
Qed.
End Products.
