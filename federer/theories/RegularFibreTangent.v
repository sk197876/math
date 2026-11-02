(** Federer (1969), 3.2.28(1), printed p. 263:
    the actual tangent to a regular fibre is the
    kernel of its differential, by 3.1.21, p. 234. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormClassOneUP NormRegularity NormOpenDomainLaws NormRankZero
  LinearRankUP LinearRankAtLeast LinearSurjectiveRank RankThresholdOpen
  ConstantRankTheorem ConstantRankFibreTangent TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope nat_scope.

(** Source for [regular_fibre_tangent]: Tan[f^{-1}{f(b)},b]
    equals ker Df(b) when Df(b) is onto, supporting
    Federer 3.2.28(1), p. 263. The regular
    neighbourhood follows from derivative continuity; an extra
    constant-rank neighbourhood is not assumed. *)
Theorem regular_fibre_tangent (R:realType) N q
    (f:R_n R N->R_n R q)
    (D:R_n R N->Hom (R_n R N) (R_n R q)) b:
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R N))
    (inner_norm (@euclidean_inner_productP R q)) (fun _=>True) f D ->
  (forall y,exists x,D b x=y) ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R N))
    [set x|f x=f b] b=[set w|D b w=0%R].
Proof.
move=>hD hSurj.
have hThreshold:=@linear_surjective_rank_at_least R (R_n R N) (R_n R q) q
  (@coordinate_basis R q) (@coordinate_basisP R q) (D b) hSurj.
have hRank:=@linear_rank_from_full_threshold R (R_n R N) (R_n R q) q
  (@coordinate_basis R q) (@coordinate_basisP R q) (D b) hThreshold.
have hqN:=@linear_rank_domain_bound R (R_n R N) (R_n R q) (D b) N
  (@coordinate_basis R N) (@coordinate_basisP R N) q hRank.
have [l hN]:exists l,N=q+l by exists (N-q); rewrite subnKC.
subst N.
pose X:=R_n R (q+l); pose Y:=R_n R q.
pose NX:=inner_norm (@euclidean_inner_productP R (q+l)).
pose NY:=inner_norm (@euclidean_inner_productP R q).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (q+l)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R q).
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
have hClass:norm_class hNX hNY (fun _=>True) f 1%N.
  apply:(@norm_class_firstP R X Y NX NY hNX hNY (fun _=>True) f).2.
  by exists D.
have [U [e [p [j [g [G [psi hC]]]]]]]:=
  @federer_3_1_18 R q l q (fun _=>True) f D b 1%N (leqnn 1) hClass hD hGeneric.
have hT:=@constant_rank_fibre_tangent R q l q (fun _=>True) U
  f D b e p j g G psi hC hD.
have hSet:[set x:X|True /\ f x=f b]=[set x:X|f x=f b].
  apply/seteqP; split=>x; first by move=>[_ hx].
  by move=>hx; split.
by rewrite hSet in hT.
Qed.
