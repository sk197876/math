(** Federer (1969), 3.1.24, p. 240: all
    derivatives of the positive square root in the quadratic
    inverse majorant, derived by ordinary product differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal NormDifferentialArithmetic
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra ScalarPowerDifferential
  ScalarReciprocalDifferential ScalarSquareRootDifferential ScalarSquareRootCoefficients
  ContinuousMultilinearUP NormHigherDifferentialUP NormClassOneUP NormClassHigherUP ScalarDerivativeSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_square_root_derivative_coefficient]:
    supporting the analytic square root used in Federer
    3.1.24, p. 240. The mth coefficient is the
    falling half-integer product times sqrt(a)/a^m, on a>0. *)
Definition scalar_square_root_derivative_coefficient (R:realType) m (a:R):R :=
  square_root_falling_coefficient m*Num.sqrt a*(a^-1)^+m.

(** Source for [scalar_square_root_derivative_zero]: the
    zeroth derivative is the original positive square root,
    supporting the scalar inverse calculation in Federer
    3.1.24, p. 240. *)
Lemma scalar_square_root_derivative_zero (R:realType) (a:R) :
  scalar_square_root_derivative_coefficient 0 a= Num.sqrt a.
Proof. by rewrite /scalar_square_root_derivative_coefficient square_root_falling_zero expr0 mul1r mulr1. Qed.

(** Source for [scalar_square_root_derivative_step_coefficient]:
    the first product rule turns the mth displayed
    coefficient into the next, supporting the quadratic inverse
    majorant in Federer 3.1.24, p. 240. *)
Lemma scalar_square_root_derivative_step_coefficient (R:realType) m (a:R) :
  0<a ->
  square_root_falling_coefficient m*
    ((2*Num.sqrt a)^-1*(a^-1)^+m+
      Num.sqrt a*(m%:R*(a^-1)^+m.-1*(-((a^-1)^+2))))=
    scalar_square_root_derivative_coefficient m.+1 a.
Proof.
move=>ha.
pose s:=Num.sqrt a.
have hs:0<s by rewrite /s sqrtr_gt0.
have hs0:s!=0 by rewrite gt_eqF.
have hsinv:(2*s)^-1= s*a^-1/2.
  have hs2:s^+2=a:=sqr_sqrtr (ltW ha).
  rewrite -hs2 expr2; by field; rewrite hs0.
rewrite /scalar_square_root_derivative_coefficient square_root_falling_successor -/s hsinv.
case:m=>[|m].
- rewrite !expr0 expr1 /= !mul0r mulr0 addr0 subr0; ring.
- rewrite [((a^-1)^+m.+1)]exprS [((a^-1)^+m.+2)]exprS
    [((a^-1)^+m.+1)]exprS expr2; ring.
Qed.

(** Source for [scalar_square_root_derivative_step]: each
    displayed coefficient is actually differentiable on the
    positive reals, with the next coefficient as derivative.
    This supports the analyticity assertion about the scalar
    inverse in Federer 3.1.24, p. 240. *)
Lemma scalar_square_root_derivative_step (R:realType) m (a:R) :
  0<a -> has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    (fun t=>0<t) (@scalar_square_root_derivative_coefficient R m) a
    (@scalar_coefficient_linear_map R R^o (scalar_square_root_derivative_coefficient m.+1 a)).
Proof.
move=>ha.
have hN:=scalar_absolute_value_norm R.
have hroot:=scalar_square_root_differential ha.
have ha0:a!=0 by rewrite gt_eqF.
have hpos0 (x:R^o) (hx:0<x):x!=0 by rewrite gt_eqF.
have hrec:=@norm_differential_restrict R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
  (fun t=>t!=0) (fun t=>0<t) (fun t=>t^-1) a
  (@scalar_coefficient_linear_map R R^o (-((a^-1)^+2)))
  hpos0 (norm_differential_interior hroot) (scalar_reciprocal_differential ha0).
have hp:=@norm_curve_power_differential R (fun x=>0<x) (fun x=>x^-1)
  a (-((a^-1)^+2)) m hrec.
have hprod:=norm_curve_scalar_product hN hroot hp.
have hscale:=norm_differential_scale hN hN (square_root_falling_coefficient m) hprod.
rewrite -scalar_coefficient_linear_scale in hscale.
change (has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  (fun t=>0<t) (fun t=>square_root_falling_coefficient m*(Num.sqrt t*(t^-1)^+m)) a
  (@scalar_coefficient_linear_map R R^o (square_root_falling_coefficient m*
    ((2*Num.sqrt a)^-1*(a^-1)^+m+
      Num.sqrt a*(m%:R*(a^-1)^+m.-1*(-((a^-1)^+2))))))) in hscale.
rewrite (scalar_square_root_derivative_step_coefficient m ha) in hscale.
apply: (norm_differential_domain_agreement hN _ hscale).
move=>t ht; rewrite /scalar_square_root_derivative_coefficient; ring.
Qed.

Section Higher.
Variable R:realType.
Variable Z:nat->lmodType R.
Variable ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o.
Variable ZN:forall i,Z i->R.
Hypothesis hZ:forall i,is_continuous_multilinear_space
  (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (@ev i) (@ZN i).

(** Source for [scalar_square_root_higher_differentials]: the
    positive square root is smooth, with actual differential
    fields given by its scalar derivative coefficients times
    the product of the arguments, supporting Federer 3.1.24,
    p. 240. Existence is proved by the derivative-sequence
    criterion, rather than assumed as calculus background. *)
Theorem scalar_square_root_higher_differentials :
  norm_class_infinity (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) ev ZN (fun t=>0<t) Num.sqrt /\
  exists D:forall i,R->Z i,
    (forall i x,0<x -> has_norm_higher_differential (fun t:R^o=>`|t|) ev ZN
      (fun t=>0<t) Num.sqrt i x (D i x)) /\
    (forall i x u,@ev i u (D i x)=
      (\prod_(j<i) u j)*scalar_square_root_derivative_coefficient i x) /\
    forall i,norm_class_zero (fun t:R^o=>`|t|) (@ZN i) (fun t=>0<t) (D i).
Proof.
have hN:=scalar_absolute_value_norm R.
have hF i a (ha:0<a):exists L:Hom R^o R^o,
    has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
      (fun t=>0<t) (scalar_square_root_derivative_coefficient i) a L /\
    forall t,L t= t*scalar_square_root_derivative_coefficient i.+1 a.
  exists (@scalar_coefficient_linear_map R R^o (scalar_square_root_derivative_coefficient i.+1 a)).
  split; first exact: scalar_square_root_derivative_step.
  by [].
have he:(@scalar_square_root_derivative_coefficient R 0)= Num.sqrt.
  apply: funext=>x; exact: scalar_square_root_derivative_zero.
split.
- have hh:=@scalar_derivative_sequence_class_infinity R R^o (fun t:R^o=>`|t|) hN
    Z ev ZN hZ (fun t=>0<t) (@scalar_square_root_derivative_coefficient R) hF.
  by rewrite he in hh.
- have [D [hD [hE hc]]]:=@scalar_derivative_sequence_differentials R R^o (fun t:R^o=>`|t|) hN
    Z ev ZN hZ (fun t=>0<t) (@scalar_square_root_derivative_coefficient R) hF.
  exists D; split; first by rewrite -he.
  by split.
Qed.
End Higher.
