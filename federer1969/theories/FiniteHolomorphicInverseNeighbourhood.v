(** Federer (1969), 3.4.12, pp. 338–339: the original
    holomorphic coordinate map with invertible differential has an
    actual local holomorphic inverse. Reuse the finite real analytic
    inverse theorem with the original paired real basis, then prove
    holomorphy from actual inverse differential identities. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexOrderedBases
  InnerProductUP InnerNorm LinearBasis NormDifferentialUP NormClassOneUP NormRegularity
  NormOpenDomainLaws NormDiffeomorphismUP FiniteAnalyticInverseNeighbourhood HolomorphicUP
  HolomorphicRestriction HolomorphicInverseFromFirst.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Inverse.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Variable B:XR->XR->R.
Variable hB:is_inner_product B.
Variable hN:is_real_norm (inner_norm hB).

(** Source for [finite_holomorphic_inverse_neighbourhood]: an actual
    holomorphic map in equal finite complex dimensions has an
    actual holomorphic inverse near each point with injective
    differential, extending 3.1.24, p. 240, under 3.4.12,
    p. 339. No inverse map or inverse holomorphy is assumed. *)
Theorem finite_holomorphic_inverse_neighbourhood n (b:'I_n->X) (hb:is_basis b)
    (A:set X) (f:X->X) (D:X->Hom XR XR) a:
  is_holomorphic hN hN A f ->
  is_norm_class_one_field (inner_norm hB) (inner_norm hB) A f D ->A a ->injective (D a) ->
  exists r:R,0<r /\(forall x,inner_norm hB (x-a)<r ->A x) /\exists g:X->X,
    is_norm_diffeomorphism hN hN [set x|inner_norm hB (x-a)<r]
      (f @` [set x|inner_norm hB (x-a)<r]) f g 1%N /\
    is_holomorphic hN hN [set x|inner_norm hB (x-a)<r] f /\
    is_holomorphic hN hN (f @` [set x|inner_norm hB (x-a)<r]) g.
Proof.
move=>hF hD ha hInjective.
have [r [hr [hRA [g [hInverse hAnalytic]]]]]:=@finite_analytic_inverse_neighbourhood R XR B hB hN
  (n+n)%N (@ordered_real_basis R X n b) (@ordered_real_basisP R X n b hb) A f D a
  hF.1 hD ha hInjective.
pose U:=[set x|inner_norm hB (x-a)<r].
pose V:=f @` U.
have hOpen x (hx:U x):@norm_domain_interior R XR (inner_norm hB) U x.
  exact:(@norm_open_ball_domain_interior R XR (inner_norm hB) hN a r x hx).
have hFU:=@holomorphic_open_restriction R X X (inner_norm hB) (inner_norm hB) hN hN A U f hRA hOpen hF.
have hMap x (hx:U x):V (f x):=norm_diffeomorphism_maps hInverse hx.
have hInverseMap y (hy:V y):U (g y):=norm_diffeomorphism_inverse_maps hInverse hy.
have hLeft x (hx:U x):g (f x)=x:=norm_diffeomorphism_left_inverse hInverse hx.
have hRight y (hy:V y):f (g y)=y:=norm_diffeomorphism_right_inverse hInverse hy.
have hG:=@holomorphic_inverse_from_first R X X (inner_norm hB) (inner_norm hB) hN hN
  V U g f hInverseMap hMap hRight hLeft (norm_diffeomorphism_inverse_class hInverse) hFU.
exists r;split;first exact:hr.
split;first exact:hRA.
exists g;split;first exact:hInverse.
by split.
Qed.
End Inverse.
