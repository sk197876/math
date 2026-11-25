(** Federer (1969), 3.2.21, p. 257: a linear
    map of rank at least mu is injective on some orthogonally
    rotated mu-dimensional coordinate block. Existence follows
    from the proved polar projection factorisation and adapted
    orthogonal coordinates, not a new choice axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  AdjointLaws InnerProductUP InnerProductLaws OrthogonalMaps CoordinateProjection PolarFactorisationUP PolarProjection
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanRightBlockProjection
  OrthogonalProjectionChartUP OrthogonalProjectionChart OrthogonalProjectionChartLaws
  LinearRankAtLeast RankThresholdEuclideanQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [rank_orthogonal_block_injection]: supporting
    choice of g in O(m) in Federer 3.2.21, p. 257.
    The last mu-coordinate convention is equivalent to the
    book's first block, by a fixed block interchange. All
    source dimensions k+mu and degree zero are allowed in this
    linear support lemma; the numbered theorem requires mu>0. *)
Lemma rank_orthogonal_block_injection (R : realType) k mu n
    (D : Hom (R_n R (k+mu)) (R_n R n)) :
  linear_rank_at_least D mu ->
  exists g : Hom (R_n R (k+mu)) (R_n R (k+mu)),
    is_orthogonal_map (@euclidean_inner_product R (k+mu))
      (@euclidean_inner_product R (k+mu)) (hom_as_linear g) /\
    injective (hom_comp D (hom_comp g (@euclidean_last_injection_map R k mu))).
Proof.
move=> hRank.
pose X := R_n R (k+mu).
pose V := R_n R mu.
pose B := @euclidean_inner_product R (k+mu).
pose C := @euclidean_inner_product R mu.
have hB := @euclidean_inner_productP R (k+mu).
have hC := @euclidean_inner_productP R mu.
have [P hP] := rank_threshold_euclidean_quotient hRank.
pose alpha := linear_comp (hom_as_linear P) (hom_as_linear D).
have hAlpha : forall y,exists x,alpha x=y := hP.
have hDim : (mu<=k+mu)%N by rewrite leq_addl.
have [K [p hFact]] := @polar_projection_factorisation_exists R X V B C hB hC
  (k+mu) (@coordinate_basis R (k+mu)) (@coordinate_basisP R (k+mu))
  mu (@coordinate_basis R mu) (@coordinate_basisP R mu) hDim alpha.
have hKSurj y : exists x,K x=y.
  have [x hx] := hAlpha y; exists (p x).
  by rewrite (projection_factor_equation hFact x).
have hKInj : injective K.
  move=> x y hEq; apply: (@inner_vectors_ext R V C hC)=> z.
  have [t ht] := hKSurj z.
  by rewrite -ht (projection_factor_symmetric hFact t x)
    (projection_factor_symmetric hFact t y) hEq.
have hp : O_star p := (O_star_projection p).2 (projection_factor_orthogonal hFact).
pose charts := @orthogonal_projection_chart R k mu p hp.
have hCharts := @orthogonal_projection_chart_specification R k mu p hp.
change (is_orthogonal_projection_chart p charts.1 charts.2) in hCharts.
pose g := hom_of_linear charts.2.
have hCoordinate x : p (g (@euclidean_last_injection R k mu x))=x.
  exact: (@projection_chart_fibre_coordinate R k mu p charts.1 charts.2 hCharts (0:R_n R k) x).
exists g; split; first exact: (projection_chart_backward_orthogonal hCharts).
move=> x y hEq; apply: hKInj.
have hx := projection_factor_equation hFact (g (@euclidean_last_injection R k mu x)).
have hy := projection_factor_equation hFact (g (@euclidean_last_injection R k mu y)).
rewrite (hCoordinate x) in hx; rewrite (hCoordinate y) in hy.
rewrite hx hy.
change (P (D (g (@euclidean_last_injection R k mu x)))=
  P (D (g (@euclidean_last_injection R k mu y)))).
exact: (congr1 P hEq).
Qed.
