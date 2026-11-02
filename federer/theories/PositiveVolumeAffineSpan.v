(** Supporting nondegeneracy for Federer (1969), 2.10.5(2), p. 173, and the
    compact convex projection-continuity passage 3.2.36, p. 272. A subset of
    R^n of positive Lebesgue outer measure has differences spanning R^n
    about each of its points. Select independent differences from the set; a
    deficient span is the image of a singular orthogonal projection and has
    measure zero by 2.7.16(1), pp. 134–135. This is a supporting lemma, not
    a separately printed claim of 2.10.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  LinearBasis FiniteSpans FiniteDimension FiniteBasisCriterion FiniteBasisComparison
  FiniteSubsetSpan GramSchmidt OrthonormalisationUP OrthonormalProjection
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueDeterminant
  EuclideanLebesgueTranslation MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_positive_volume_difference_basis]:
    supporting full affine span for the convex
    geometry behind Federer 2.10.5(2), p. 173,
    and 3.2.36, p. 272. Positive outer measure
    suffices; no measurability or convexity
    hypothesis is added to this algebraic step. *)
Theorem euclidean_positive_volume_difference_basis (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a : inner_metric_space (@euclidean_inner_productP R n)) :
  S a -> (0<euclidean_lebesgue_measure n S)%E ->
  exists e : 'I_n -> R_n R n, is_basis e /\ forall i, S (e i+a).
Proof.
move=> ha hpos.
pose V := R_n R n.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose D : set V := [set v | S (v+a)].
have [k [e [hkn [hi [heD hspan]]]]] :=
  @finite_subset_independent_span R V n (@coordinate_basis R n) (@coordinate_basisP R n) D.
have hknE : k=n.
  case: (eqVneq k n)=> [he|hne]; first exact he.
  exfalso; have hlt : (k<n)%N by rewrite ltn_neqAle hne hkn.
  have [u hu] := @gram_schmidt_exists R V (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) k e hi.
  have ho := orthonormalisation_orthonormal hu.
  pose p : {linear V -> V} := GRing.Linear.clone _ _ _ _
    (orthonormal_projection (@euclidean_inner_productP R n) u) _.
  have hdet : euclidean_det p=0.
    case: (eqVneq (euclidean_det p) 0)=> [hzero|hnon]; first exact hzero.
    exfalso.
    have hinj := (euclidean_det_injective p).1 hnon.
    have hfull x : in_finite_span e x.
      have [z hz] := euclidean_injective_surjective hinj x.
      apply: (orthonormalisation_span hu x).2; rewrite -hz.
      exact: orthonormal_projection_in_span.
    have hb := finite_basis_criterion hi hfull.
    have hsize := finite_basis_size hb (@coordinate_basisP R n).
    by rewrite hsize ltnn in hlt.
  pose T : set E := (p : E -> E) @` setT.
  have hT : euclidean_lebesgue_measure n T=0%:E.
    by rewrite /T euclidean_lebesgue_linear_image hdet normr0 mul0e.
  have hsub : S `<=` [set a+x | x in T].
    move=> x hx.
    have hv : D (x-a) by rewrite /D /= subrK.
    have hpfix : p (x-a)=x-a.
      change (orthonormal_projection (@euclidean_inner_productP R n) u (x-a)=x-a).
      apply: (@orthonormal_projection_fixed R V (@euclidean_inner_product R n)
        (@euclidean_inner_productP R n) k u ho (x-a)).
      exact: (orthonormalisation_span hu (x-a)).1 (hspan (x-a) hv).
    exists (x-a); last by rewrite addrC subrK.
    exists (x-a)=> //.
  have hb := measure_mono (euclidean_lebesgue_is_measure R n) hsub.
  rewrite euclidean_lebesgue_translation hT in hb.
  by have := lt_le_trans hpos hb; rewrite ltxx.
subst k; exists e; split; last exact heD.
apply: (@finite_independent_basis R (finite_basis_vect (@coordinate_basisP R n)) n e)=> //.
by rewrite finite_basis_dimension card_ord.
Qed.
