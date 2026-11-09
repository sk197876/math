(** Federer (1969), 3.4.5, p. 321: the actual
    analytic coordinate change used in the cubic-cone
    counterexample argument. This is the analytic inverse
    assertion of 3.1.24, p. 240, on its original domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm LinearBasis
  NormDifferentialUP NormClassOneUP NormRegularity NormOpenDomainLaws NormDiffeomorphismUP
  FiniteLocalDiffeomorphism NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormAnalyticInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_inverse_neighbourhood]: an
    actual analytic map with an injective differential
    in equal finite dimensions has an actual local
    analytic inverse, supporting the example of 3.4.5,
    p. 321. No inverse map or inverse regularity
    is assumed. *)
Theorem finite_analytic_inverse_neighbourhood (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) (hN:is_real_norm (inner_norm hB))
    m (b:'I_m->X) (hb:is_basis b) (A:set X) (f:X->X) (D:X->Hom X X) a:
  @norm_analytic R X X (inner_norm hB) (inner_norm hB) hN hN A f ->
  is_norm_class_one_field (inner_norm hB) (inner_norm hB) A f D ->
  A a ->injective (D a) ->
  exists r:R,0<r /\
    (forall x,inner_norm hB (x-a)<r ->A x) /\
    exists g:X->X,
      is_norm_diffeomorphism hN hN [set x|inner_norm hB (x-a)<r]
        (f @` [set x|inner_norm hB (x-a)<r]) f g 1%N /\
      @norm_analytic R X X (inner_norm hB) (inner_norm hB) hN hN
        (f @` [set x|inner_norm hB (x-a)<r]) g.
Proof.
move=>hf hD ha hInjective.
have hf1:=norm_analytic_class_all_orders hf 1%N.
have [r [hr [hRA [g hInverse]]]]:=@finite_local_diffeomorphism R X B hB hN m b hb
  A f D a 1%N hf1 hD ha hInjective.
pose U:=[set x|inner_norm hB (x-a)<r].
pose V:=f @` U.
have hOpen x (hx:U x):norm_domain_interior (inner_norm hB) U x.
  exact:(@norm_open_ball_domain_interior R X (inner_norm hB) hN a r x hx).
have hfU:=norm_analytic_open_restriction hRA hOpen hf.
have hMap x (hx:U x):V (f x):=norm_diffeomorphism_maps hInverse hx.
have hInverseMap y (hy:V y):U (g y):=norm_diffeomorphism_inverse_maps hInverse hy.
have hLeft x (hx:U x):g (f x)=x:=norm_diffeomorphism_left_inverse hInverse hx.
have hRight y (hy:V y):f (g y)=y:=norm_diffeomorphism_right_inverse hInverse hy.
have hg:=@norm_analytic_inverse_from_first R X X (inner_norm hB) (inner_norm hB) hN hN
  V U g f hInverseMap hMap hRight hLeft (norm_diffeomorphism_inverse_class hInverse) hfU.
exists r;split;first exact:hr.
split;first exact:hRA.
by exists g.
Qed.
