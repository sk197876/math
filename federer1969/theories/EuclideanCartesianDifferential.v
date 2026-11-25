(** Federer (1969), 3.2.23, p. 260: differentiation of f times g
    at an actual pair of differentiability points. The chain rule and
    two coordinate inclusions prove the product differential, without
    choosing a derivative field or using a constructed calculus library. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanCartesianLinear NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialLocal NormDifferentialFiniteCalculus
  NormDifferentialArithmetic NormFiniteLinearBound NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_differential_linear_precompose]: supporting
    coordinate chain rule in Federer 3.2.23, p. 260, by 3.1.1(2),
    p. 210. The input is the actual differential at the projected
    point; no global derivative field or rank assumption is introduced. *)
Lemma euclidean_differential_linear_precompose (R:realType) d m n
    (f:R_n R m->R_n R n) (P:Hom (R_n R d) (R_n R m)) a
    (D:Hom (R_n R m) (R_n R n)):
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f (P a) D ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R d))
    (inner_norm (@euclidean_inner_productP R n)) setT (fun x=>f (P x)) a (hom_comp D P).
Proof.
move=>hD.
pose hX:=inner_norm_real_norm (@euclidean_inner_productP R d).
pose hM:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hY:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hP:=norm_finite_linear_bounded hX hM (@coordinate_basisP R d) P.
have hDP:=norm_differential_linear hX hM (@norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) a) hP.
have hComp:=norm_differential_chain hX hM hY hDP hD.
exact:(norm_differential_restrict (fun _ _=>conj Logic.I Logic.I)
  (@norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) a) hComp).
Qed.

(** Source for [euclidean_cartesian_differential]: the actual
    identity D(f times g)(x,y)=Df(x) times Dg(y) behind the
    displayed integral in Federer 3.2.23, p. 260. The factors
    need only be differentiable at this pair; zero-dimensional
    source and target blocks are included. *)
Theorem euclidean_cartesian_differential (R:realType) m mu n v
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R v) p
    (A:Hom (R_n R m) (R_n R n)) (B:Hom (R_n R mu) (R_n R v)):
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f (euclidean_block_split p).1 A ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
    (inner_norm (@euclidean_inner_productP R v)) setT g (euclidean_block_split p).2 B ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R (m+mu)))
    (inner_norm (@euclidean_inner_productP R (n+v))) setT
    (euclidean_cartesian_map f g) p (euclidean_cartesian_linear A B).
Proof.
move=>hF hG.
pose hX:=inner_norm_real_norm (@euclidean_inner_productP R (m+mu)).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hV:=inner_norm_real_norm (@euclidean_inner_productP R v).
pose hY:=inner_norm_real_norm (@euclidean_inner_productP R (n+v)).
pose P:=@euclidean_first_block_map R m mu.
pose Q:=@euclidean_last_block_map R m mu.
pose i:=@euclidean_first_injection_map R n v.
pose j:=@euclidean_last_injection_map R n v.
have hFP:=@euclidean_differential_linear_precompose R (m+mu) m n f P p A hF.
have hGQ:=@euclidean_differential_linear_precompose R (m+mu) mu v g Q p B hG.
have hI:=norm_finite_linear_bounded hN hY (@coordinate_basisP R n) i.
have hJ:=norm_finite_linear_bounded hV hY (@coordinate_basisP R v) j.
have hIP:=norm_differential_postcompose hX hFP hI.
have hJQ:=norm_differential_postcompose hX hGQ hJ.
have hSum:=norm_differential_add hY hIP hJQ.
apply:(norm_differential_domain_agreement hX _ hSum)=>x _.
symmetry; exact:euclidean_block_join_sum.
Qed.
