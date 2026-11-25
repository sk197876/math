(** Federer (1969), 3.4.5, p. 321: the flat
    coefficient in the cited local/global example is analytic
    away from its flat endpoint. The smooth flat function
    itself was proved in 3.1.11, p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticDomain NormAnalyticConstant
  NormAnalyticOperations NormAnalyticArithmeticLocal NormAnalyticScalarProducts
  RealExponentialSealed FlatExponentialUP FlatExponentialSealed
  RealExponentialAnalytic ScalarReciprocalAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatAnalytic.
Variable R:realType.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation AN A f:=(@norm_analytic R R^o R^o N N hN hN A f).

(** Source for [scalar_positive_domain_interior]: the positive
    branch of the flat coefficient has its original open
    domain, supporting 3.4.5, p. 321. *)
Lemma scalar_positive_domain_interior (x:R^o):0<x ->norm_domain_interior N (fun t=>0<t) x.
Proof.
move=>hx;exists x;split;first exact:hx.
move=>h hh;have hb:=ler_norm (-h);rewrite normrN in hb;lra.
Qed.

(** Source for [scalar_negative_domain_interior]: the zero
    branch has an actual negative open neighbourhood,
    supporting the example cited in 3.4.5, p. 321. *)
Lemma scalar_negative_domain_interior (x:R^o):x<0 ->norm_domain_interior N (fun t=>t<0) x.
Proof.
move=>hx;exists (-x);split;first by rewrite oppr_gt0.
move=>h hh;have hb:=ler_norm h;lra.
Qed.

(** Source for [flat_exponential_positive_analytic]: the
    actual exp(-t^-2) branch is analytic for t>0,
    supporting the example cited in 3.4.5, p. 321. *)
Theorem flat_exponential_positive_analytic:AN (fun t=>0<t) (@FlatExponential.value R).
Proof.
pose NZ:=fun t:R^o=>t!=0.
have hInv:AN NZ (fun t=>t^-1):=@scalar_reciprocal_analytic R.
have hSquare:AN NZ (fun t=>t^-1*t^-1):=norm_analytic_scalar_product hInv hInv.
have hNegative:AN NZ (fun t=> -(t^-1*t^-1)).
  move=>a ha;exact:(norm_analytic_at_negate (hSquare a ha)).
have hExpression:AN NZ (fun t=>RealExponential.exponential (-(t^-1*t^-1))).
  exact:(norm_analytic_compose_on (fun t ht=>Logic.I) hNegative (@real_exponential_analytic R)).
have hPositive:AN (fun t=>0<t) (fun t=>RealExponential.exponential (-(t^-1*t^-1))).
  apply:(norm_analytic_open_restriction _ scalar_positive_domain_interior hExpression).
  move=>t ht;by rewrite /NZ gt_eqF.
apply:(norm_analytic_domain_agreement _ hPositive)=>t ht.
by rewrite (flat_exponential_positive_value (@FlatExponential.laws R) ht) expr2.
Qed.

(** Source for [flat_exponential_negative_analytic]: the
    original zero branch is analytic at every negative point,
    supporting the example cited in 3.4.5, p. 321. *)
Theorem flat_exponential_negative_analytic:AN (fun t=>t<0) (@FlatExponential.value R).
Proof.
have hConstant:AN (fun t=>t<0) (fun _=>0):=
  @norm_constant_analytic R R^o R^o N N hN hN (fun t=>t<0) scalar_negative_domain_interior 0.
apply:(norm_analytic_domain_agreement _ hConstant)=>t ht.
symmetry;exact:(flat_exponential_nonpositive_value (@FlatExponential.laws R) (ltW ht)).
Qed.

(** Source for [flat_exponential_off_origin_analytic]: both
    actual branches are analytic on the original complement
    of zero. No analyticity is claimed at the flat point,
    supporting 3.4.5, p. 321. *)
Theorem flat_exponential_off_origin_analytic:AN (fun t=>t!=0) (@FlatExponential.value R).
Proof.
have hPosNZ (t:R^o) (ht:0<t):t!=0 by rewrite gt_eqF.
have hNegNZ (t:R^o) (ht:t<0):t!=0 by rewrite lt_eqF.
move=>a ha;case:(ltP 0 a)=>[hPositive|hNonpositive].
- have hNear:=@flat_exponential_positive_analytic a hPositive.
  have hResult:=@norm_analytic_at_domain_enlargement R R^o R^o N N hN hN
    (fun t=>0<t) (fun t=>t!=0) (@FlatExponential.value R) a hPosNZ hNear.
  exact hResult.
- have hNegative:a<0 by rewrite lt_neqAle ha hNonpositive.
  have hNear:=@flat_exponential_negative_analytic a hNegative.
  have hResult:=@norm_analytic_at_domain_enlargement R R^o R^o N N hN hN
    (fun t=>t<0) (fun t=>t!=0) (@FlatExponential.value R) a hNegNZ hNear.
  exact hResult.
Qed.
End FlatAnalytic.
