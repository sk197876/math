(** Federer (1969), 3.4.8(10), pp. 331–332:
    apply the existing finite analytic inverse
    theorem from a differential at the
    original point. The global derivative field
    is supplied by proved analytic regularity. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm LinearBasis NormDifferentialUP
  NormDifferentialDirectional NormClassOneUP NormRegularity NormDiffeomorphismUP
  NormAnalyticUP NormAnalyticLocal FiniteAnalyticInverseNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_inverse_from_point_differential]:
    the joint equation map has an
    actual analytic local inverse whenever
    its original differential is injective,
    3.4.8(10), pp. 331–332. Apply
    the proved analytic inverse theorem;
    no inverse, chart or extra regularity
    field is assumed. *)
Theorem finite_analytic_inverse_from_point_differential (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) (hN:is_real_norm (inner_norm hB))
    n (e:'I_n->X) (he:is_basis e) (A:set X) (f:X->X) a (L:Hom X X):
  @norm_analytic R X X (inner_norm hB) (inner_norm hB) hN hN A f ->
  A a ->has_norm_differential (inner_norm hB) (inner_norm hB) A f a L ->injective L ->
  exists r:R,0<r /\(forall x,inner_norm hB (x-a)<r ->A x) /\
    exists g:X->X,
      is_norm_diffeomorphism hN hN [set x|inner_norm hB (x-a)<r]
        (f @` [set x|inner_norm hB (x-a)<r]) f g 1%N /\
      @norm_analytic R X X (inner_norm hB) (inner_norm hB) hN hN
        (f @` [set x|inner_norm hB (x-a)<r]) g.
Proof.
move=>hf ha hL hInjective.
have [D hD]:=(norm_class_firstP hN hN A f).1 (norm_analytic_class_all_orders hf 1%N).
have hAt:=norm_class_one_differential hD ha.
have hEqual:D a = L:=NormDifferentialDirectional.norm_differential_unique hN hN hAt hL.
have hDInjective:injective (D a) by rewrite hEqual.
exact:(@finite_analytic_inverse_neighbourhood R X B hB hN n e he A f D a hf hD ha hDInjective).
Qed.
