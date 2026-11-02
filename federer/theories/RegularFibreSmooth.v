(** Federer (1969), 3.2.28(1), printed p. 263:
    a smooth regular fibre has fixed local straightening
    charts of every finite class, by the class-infinity
    constant-rank theorem of 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormClassOneUP NormRegularity NormOpenDomainLaws NormRankZero
  LinearRankUP LinearRankAtLeast LinearSurjectiveRank RankThresholdOpen
  ConstantRankSmooth ConstantRankSmoothFibreStraightening
  FiniteInnerSmoothSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope nat_scope.

(** Source for [regular_fibre_smooth_submanifold]: the
    class-infinity regular-level conclusion used in Federer
    3.2.28(1), p. 263. The same local maps,
    inverse maps, domains and vector plane work at every
    derivative order; none depend on the requested finite class. *)
Theorem regular_fibre_smooth_submanifold (R:realType) N q
    (f:R_n R N->R_n R q)
    (D:R_n R N->Hom (R_n R N) (R_n R q)) (c:R_n R q):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R N))
    (inner_norm_real_norm (@euclidean_inner_productP R q)) (fun _=>True) f ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R N))
    (inner_norm (@euclidean_inner_productP R q)) (fun _=>True) f D ->
  (forall b,f b=c ->forall y,exists x,D b x=y) ->
  @is_euclidean_smooth_submanifold R N (N-q) [set x|f x=c].
Proof.
move=>hf hD hSurj b hb.
have hThreshold:=@linear_surjective_rank_at_least R (R_n R N) (R_n R q) q
  (@coordinate_basis R q) (@coordinate_basisP R q) (D b) (hSurj b hb).
have hRank:=@linear_rank_from_full_threshold R (R_n R N) (R_n R q) q
  (@coordinate_basis R q) (@coordinate_basisP R q) (D b) hThreshold.
have hqN:=@linear_rank_domain_bound R (R_n R N) (R_n R q) (D b) N
  (@coordinate_basis R N) (@coordinate_basisP R N) q hRank.
have [l hN]:exists l,N=q+l by exists (N-q); rewrite subnKC.
subst N; rewrite addKn.
pose X:=R_n R (q+l); pose Y:=R_n R q.
pose NX:=inner_norm (@euclidean_inner_productP R (q+l)).
have [r [hr hBall]]:=@rank_threshold_interior R X Y NX
  (@euclidean_inner_product R (q+l)) (@euclidean_inner_product R q)
  (@euclidean_inner_productP R (q+l)) (@euclidean_inner_productP R q)
  (q+l) (@coordinate_basis R (q+l)) (@coordinate_basisP R (q+l)) erefl
  (fun _=>True) D (fun x _=>@norm_full_domain_interior R X NX x)
  (norm_class_one_continuity hD) b q I hThreshold.
have hGeneric:norm_generic_rank NX (fun _=>True) D b q.
  exists r; split=>// h hh; split; first exact:I.
  exact:(@linear_rank_from_full_threshold R X Y q
    (@coordinate_basis R q) (@coordinate_basisP R q) (D ((b+h)%R)) (hBall h hh).2).
have [U [e [p [j [g [G [psi hC]]]]]]]:=
  @federer_3_1_18_smooth R q l q (fun _=>True) f D b hf hD hGeneric.
have [C [s [t [Z hStraight]]]]:=
  @constant_rank_smooth_fibre_straightening R q l q f D b U e p j g G psi hC.
exists U,C,s,t,Z; move=>k.
have h:=hStraight k; by rewrite hb in h.
Qed.
