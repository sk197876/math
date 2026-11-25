(** Private finite-expression proof for the scalar
    composition used in Federer (1969), 3.1.11,
    p. 223. Differentiating a finite
    expression uses only the already proved
    first sum, product, and chain rules.
    Public use is through ScalarSmoothCompositionSealed. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra
  ScalarSmoothSequenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_chain_expression]:
    auxiliary finite expressions in the derivatives
    of two scalar functions, supporting the
    smooth composition used in Federer
    3.1.11, p. 223. *)
Inductive scalar_chain_expression (R : realType) : Type :=
  (** Source for [SCEConstant]: constants in
      the supporting differentiation computation
      for Federer 3.1.11, p. 223. *)
  | SCEConstant : R->scalar_chain_expression R
  (** Source for [SCEOuter]: derivatives of
      the outer function at the inner value,
      supporting Federer 3.1.11, p. 223. *)
  | SCEOuter : nat->scalar_chain_expression R
  (** Source for [SCEInner]: derivatives of
      the inner function, supporting Federer
      3.1.11, p. 223. *)
  | SCEInner : nat->scalar_chain_expression R
  (** Source for [SCEAdd]: finite addition
      in the supporting derivative expressions
      for Federer 3.1.11, p. 223. *)
  | SCEAdd : scalar_chain_expression R->scalar_chain_expression R->scalar_chain_expression R
  (** Source for [SCEMultiply]: finite products
      in the supporting derivative expressions
      for Federer 3.1.11, p. 223. *)
  | SCEMultiply : scalar_chain_expression R->scalar_chain_expression R->scalar_chain_expression R.
Arguments SCEConstant {R} _.
Arguments SCEOuter {R} _.
Arguments SCEInner {R} _.
Arguments SCEAdd {R} _ _.
Arguments SCEMultiply {R} _ _.

(** Source for [scalar_chain_evaluate]:
    interpretation of the auxiliary finite
    derivative expressions for the scalar
    composition in Federer 3.1.11, p. 223. *)
Fixpoint scalar_chain_evaluate (R : realType) (F G : nat->R->R)
    (e : scalar_chain_expression R) x : R :=
  match e with
  | SCEConstant c=>c
  | SCEOuter i=>F i (G 0%N x)
  | SCEInner j=>G j x
  | SCEAdd u v=>scalar_chain_evaluate F G u x+scalar_chain_evaluate F G v x
  | SCEMultiply u v=>scalar_chain_evaluate F G u x*scalar_chain_evaluate F G v x
  end.

(** Source for [scalar_chain_derive]:
    the first sum, product and chain rules
    transform finite derivative expressions into
    finite derivative expressions, supporting the
    smooth composition in Federer 3.1.11, p. 223. *)
Fixpoint scalar_chain_derive (R : realType) (e : scalar_chain_expression R) :=
  match e with
  | SCEConstant _=>SCEConstant 0
  | SCEOuter i=>SCEMultiply (SCEOuter i.+1) (SCEInner 1)
  | SCEInner j=>SCEInner j.+1
  | SCEAdd u v=>SCEAdd (scalar_chain_derive u) (scalar_chain_derive v)
  | SCEMultiply u v=>SCEAdd
      (SCEMultiply (scalar_chain_derive u) v)
      (SCEMultiply u (scalar_chain_derive v))
  end.

(** Source for [scalar_chain_evaluate_differential]:
    every formal expression update is justified
    by an actual norm differential, supporting
    the smooth composition in Federer
    3.1.11, p. 223. *)
Theorem scalar_chain_evaluate_differential (R : realType) (F G : nat->R->R) :
  (forall i a, has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun _=>True) (F i) a
    (@scalar_coefficient_linear_map R R^o (F i.+1 a))) ->
  (forall i a, has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun _=>True) (G i) a
    (@scalar_coefficient_linear_map R R^o (G i.+1 a))) ->
  forall e a, has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun _=>True) (scalar_chain_evaluate F G e) a
    (@scalar_coefficient_linear_map R R^o (scalar_chain_evaluate F G (scalar_chain_derive e) a)).
Proof.
move=> hF hG e a.
have hN := @scalar_absolute_value_norm R.
have hwhole : norm_domain_interior (fun t : R^o=>`|t|) (fun _=>True) a.
  exists 1; split; first exact: ltr01; by move=> h _.
elim: e=>[c|i|i|u ihu v ihv|u ihu v ihv] /=.
- rewrite scalar_coefficient_linear_zero.
  exact (@norm_differential_constant R R^o R^o (fun t=>`|t|)
    (fun t=>`|t|) hN hN (fun _=>True) a c hwhole).
- have hc := norm_curve_chain_on_domain hN (fun t ht=>I)
    (hG 0%N a) (hF i (G 0%N a)).
  have he : G 1%N a*:(F i.+1 (G 0%N a) : R^o)=F i.+1 (G 0%N a)*G 1%N a.
    change (G 1%N a*F i.+1 (G 0%N a)=F i.+1 (G 0%N a)*G 1%N a).
    exact: mulrC.
  by rewrite he in hc.
- exact: hG.
- have hh := norm_differential_add hN ihu ihv.
  by rewrite -scalar_coefficient_linear_add in hh.
- exact (norm_curve_scalar_product hN ihu ihv).
Qed.

(** Source for [scalar_smooth_composition_derivatives_exists]:
    the scalar composition used to define
    the second smooth function in Federer
    3.1.11, p. 223, has derivatives
    of every order. Its witnesses are built
    only after the first-order expression rule
    has been proved. *)
Theorem scalar_smooth_composition_derivatives_exists (R : realType)
    (f g : R->R) (F G : nat->R->R) :
  is_scalar_smooth_derivative_sequence f F ->
  is_scalar_smooth_derivative_sequence g G ->
  exists H : nat->R->R,
    is_scalar_smooth_derivative_sequence (fun x=>f (g x)) H.
Proof.
move=> [hF0 hF] [hG0 hG].
pose e k := iter k (@scalar_chain_derive R) (@SCEOuter R 0).
pose H k := scalar_chain_evaluate F G (e k).
exists H; split.
- move=>x; by rewrite /H /e /= hF0 hG0.
- move=>k a.
  have he : e k.+1=scalar_chain_derive (e k) by rewrite /e iterS.
  rewrite /H he.
  exact (@scalar_chain_evaluate_differential R F G hF hG (e k) a).
Qed.
