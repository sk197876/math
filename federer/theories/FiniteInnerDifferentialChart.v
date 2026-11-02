(** Federer (1969), 3.2.28, pp. 265–267:
    isometric ambient coordinates conjugate the actual
    differential by the source and target linear maps,
    as required by 3.1.1(2), p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm
  HilbertFormCompactness OrthogonalMaps FiniteInnerChartUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialLocal NormOpenDomainLaws NormLinearIsometryInverse NormSourceChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_inner_differential_chart]: the
    actual derivative p_Y Df(x) e_X in the
    Euclidean identifications used by Federer 3.2.28,
    pp. 265–267, by the chain rule 3.1.1(2),
    p. 210. The original point and full-domain
    differential are retained exactly. *)
Theorem finite_inner_differential_chart (R:realType) (X Y:lmodType R)
    (B:X->X->R) (C:Y->Y->R) (hB:is_inner_product B) (hC:is_inner_product C)
    n k (e:Hom (R_n R n) X) (p:Hom X (R_n R n)) (t:Hom Y (R_n R k))
    (F:X->Y) a (L:Hom X Y):
  is_finite_inner_chart B e p ->
  is_orthogonal_map C (@euclidean_inner_product R k) (hom_as_linear t) ->
  has_norm_differential (inner_norm hB) (inner_norm hC) (fun _=>True) F a L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R k)) (fun _=>True)
    (fun z=>t (F (e z))) (p a) (hom_comp t (hom_comp L e)).
Proof.
move=>hChart hT hF.
pose hNX:=inner_norm_real_norm hB.
pose hNY:=inner_norm_real_norm hC.
pose hNn:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNk:=inner_norm_real_norm (@euclidean_inner_productP R k).
have hE:norm_bounded_linear (inner_norm (@euclidean_inner_productP R n)) (inner_norm hB) e.
  apply:norm_linear_isometry_bounded=>z; exact:(@finite_inner_chart_norm R X B hB n e p hChart z).
have hTBound:norm_bounded_linear (inner_norm hC) (inner_norm (@euclidean_inner_productP R k)) t.
  apply:norm_linear_isometry_bounded=>y.
  exact:(orthogonal_map_norm hC (@euclidean_inner_productP R k) hT y).
have hDE:=@norm_differential_linear R (R_n R n) X
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm hB) hNn hNX
  (fun _=>True) (p a) e (@norm_full_domain_interior R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (p a)) hE.
have hFAt:has_norm_differential (inner_norm hB) (inner_norm hC) (fun _=>True) F (e (p a)) L.
  by rewrite (finite_inner_chart_right_inverse hChart).
have hChain:=@norm_differential_chain R (R_n R n) X Y
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm hB) (inner_norm hC)
  hNn hNX hNY (fun _=>True) (fun _=>True) e F (p a) e L hDE hFAt.
have hPre:has_norm_differential (inner_norm (@euclidean_inner_productP R n)) (inner_norm hC)
    (fun _=>True) (fun z=>F (e z)) (p a) (hom_comp L e).
  apply:(norm_differential_restrict _ _ hChain).
  - by move=>z _; split.
  - exact:norm_full_domain_interior.
exact:(@norm_differential_linear_postcompose R (R_n R n) Y (R_n R k)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm hC)
  (inner_norm (@euclidean_inner_productP R k)) hNn hNY hNk (fun _=>True)
  (fun z=>F (e z)) (p a) (hom_comp L e) t hPre hTBound).
Qed.
