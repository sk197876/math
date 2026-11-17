(** Federer (1969), 3.4.12, p. 339: apply the proved
    holomorphic inverse theorem using the actual differential at
    the original point. Analytic regularity supplies the derivative
    field; ordinary differential uniqueness identifies its value. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  InnerProductUP InnerNorm LinearBasis NormDifferentialUP NormDifferentialDirectional
  NormClassOneUP NormRegularity NormDiffeomorphismUP NormAnalyticLocal HolomorphicUP
  FiniteHolomorphicInverseNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [finite_holomorphic_inverse_from_point_differential]:
    the original joint equation map has a local holomorphic
    inverse when its actual differential is injective, 3.4.12,
    p. 339. Reuse the finite inverse theorem without adding
    a derivative-field or inverse-existence premise. *)
Theorem finite_holomorphic_inverse_from_point_differential (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (B:restricted_space (ComplexScalars.embed R) X->restricted_space (ComplexScalars.embed R) X->R)
    (hB:is_inner_product B) (hN:is_real_norm (inner_norm hB))
    n (e:'I_n->X) (he:is_basis e) (A:set X) (f:X->X) a
    (L:Hom (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) X)):
  @is_holomorphic R X X (inner_norm hB) (inner_norm hB) hN hN A f ->
  A a ->@has_norm_differential R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) X) (inner_norm hB) (inner_norm hB) A f a L ->
  injective L ->exists r:R,0<r /\(forall x,inner_norm hB (x-a)<r ->A x) /\
    exists g:X->X,
      is_norm_diffeomorphism hN hN [set x|inner_norm hB (x-a)<r]
        (f @` [set x|inner_norm hB (x-a)<r]) f g 1%N /\
      @is_holomorphic R X X (inner_norm hB) (inner_norm hB) hN hN
        [set x|inner_norm hB (x-a)<r] f /\
      @is_holomorphic R X X (inner_norm hB) (inner_norm hB) hN hN
        (f @` [set x|inner_norm hB (x-a)<r]) g.
Proof.
move=>hF ha hL hInjective.
have [D hD]:=(norm_class_firstP hN hN A f).1
  (norm_analytic_class_all_orders hF.1 1%N).
have hAt:=norm_class_one_differential hD ha.
have hEqual:D a=L:=norm_differential_unique hN hN hAt hL.
have hDInjective:injective (D a) by rewrite hEqual.
exact:(@finite_holomorphic_inverse_neighbourhood R X B hB hN n e he A f D a
  hF hD ha hDInjective).
Qed.
