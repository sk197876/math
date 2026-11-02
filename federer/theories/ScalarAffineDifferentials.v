(** Federer (1969), 3.1.24, p. 240: the actual
    higher differential fields of the linear term in the
    scalar rational inverse majorant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorUP Hom RealNormUP NormDifferentialUP NormDifferentialLocal NormDifferentialLinear
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra NormAffineDilationDifferentials
  ContinuousMultilinearUP NormHigherDifferentialUP NormClassOneUP NormClassHigherUP ScalarDerivativeSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_affine_derivative_coefficient]: the
    successive scalar coefficients of b*x+c are its value,
    its slope b, and zero in every higher order, supporting
    the scalar inverse in Federer 3.1.24, p. 240. *)
Definition scalar_affine_derivative_coefficient (R:realType) (b c:R) m (x:R):R :=
  match m with 0%N=>b*x+c | 1%N=>b | _=>0 end.

(** Source for [scalar_affine_derivative_step]: the recursive
    affine derivative coefficients are actual ordinary derivatives
    on any open scalar domain, supporting Federer 3.1.24,
    p. 240. No value at a missing domain point is used. *)
Lemma scalar_affine_derivative_step (R:realType) (b c:R) (A:R->Prop)
    (hA:forall x,A x -> norm_domain_interior (fun t:R^o=>`|t|) A x) m x :
  A x -> has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    A (scalar_affine_derivative_coefficient b c m) x
    (@scalar_coefficient_linear_map R R^o (scalar_affine_derivative_coefficient b c m.+1 x)).
Proof.
move=>hx.
pose hN:=scalar_absolute_value_norm R.
case:m=>[|[|m]].
- have hh:=@norm_affine_dilation_differential R R^o (fun t=>`|t|) hN b c x.
  have he:b*:hom_of_linear (linear_id R^o)= @scalar_coefficient_linear_map R R^o b.
    apply:hom_ext=>t; change (b*t=t*b); exact:mulrC.
  rewrite he in hh.
  exact (@norm_differential_restrict R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (fun _=>True) A (fun t=>b*t+c) x _ (fun _ _=>Logic.I) (@hA x hx) hh).
- change (has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) A (fun _=>b) x
    (@scalar_coefficient_linear_map R R^o 0)).
  rewrite scalar_coefficient_linear_zero; exact (@norm_differential_constant R R^o R^o
    (fun t=>`|t|) (fun t=>`|t|) hN hN A x b (@hA x hx)).
- change (has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) A (fun _=>0) x
    (@scalar_coefficient_linear_map R R^o 0)).
  rewrite scalar_coefficient_linear_zero; exact (@norm_differential_constant R R^o R^o
    (fun t=>`|t|) (fun t=>`|t|) hN hN A x 0 (@hA x hx)).
Qed.

(** Source for [scalar_affine_higher_differentials]: the affine
    map has all actual higher differentials, with the product
    of scalar arguments times the stated coefficient, supporting
    the inverse-majorant argument in Federer 3.1.24, p. 240. *)
Theorem scalar_affine_higher_differentials (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (@ev i) (@ZN i))
    (A:R->Prop) (hA:forall x,A x -> norm_domain_interior (fun t:R^o=>`|t|) A x) (b c:R) :
  norm_class_infinity (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) ev ZN A (fun x=>b*x+c) /\
  exists D:forall i,R->Z i,
    (forall i x,A x -> has_norm_higher_differential (fun t:R^o=>`|t|) ev ZN A (fun x=>b*x+c) i x (D i x)) /\
    (forall i x u,@ev i u (D i x)=(\prod_(j<i) u j)*scalar_affine_derivative_coefficient b c i x) /\
    forall i,norm_class_zero (fun t:R^o=>`|t|) (@ZN i) A (D i).
Proof.
pose hN:=scalar_absolute_value_norm R.
pose F:=scalar_affine_derivative_coefficient b c.
have hF i x (hx:A x):exists L:Hom R^o R^o,
    has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) A (F i) x L /\
    forall t,L t= t*F i.+1 x.
  exists (@scalar_coefficient_linear_map R R^o (F i.+1 x)); split.
  - exact (@scalar_affine_derivative_step R b c A hA i x hx).
  - by [].
have hc:=@scalar_derivative_sequence_class_infinity R R^o (fun t=>`|t|) hN Z ev ZN hZ A F hF.
have [D [hD [hE hCont]]]:=@scalar_derivative_sequence_differentials R R^o (fun t=>`|t|) hN Z ev ZN hZ A F hF.
split; first exact hc.
exists D; split; first exact hD; by split.
Qed.
