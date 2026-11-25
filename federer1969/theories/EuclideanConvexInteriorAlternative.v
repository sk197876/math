(** Federer (1969), 3.2.35, p. 272:
    convex sources either have an actual interior
    point or have ambient-null closure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerConvex LinearBasis FiniteSpans FiniteDimension FiniteBasisCriterion FiniteBasisComparison
  FiniteSubsetSpan GramSchmidt OrthonormalisationUP OrthonormalProjection EuclideanLinearMaps
  ConvexProjectionSectionBuffer EuclideanSingularAffineRange EuclideanLebesgueDimensions InnerTranslationNeighbourhood TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_convex_interior_or_null_closure]:
    supporting the unrestricted convex-source
    reduction in Steiner's formula, Federer
    3.2.35, p. 272. Select a maximal
    independent family of original source differences.
    A full family gives a genuine interior
    simplex buffer. A deficient family gives a
    singular orthogonal projection fixing all original
    differences, hence an ambient-null source closure.
    No positive source mass, source measurability,
    affine basis or interior point is assumed. *)
Theorem euclidean_convex_interior_or_null_closure (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->
  (exists b,interior S b) \/euclidean_lebesgue_measure n (closure S)=0%E.
Proof.
move=>[a ha] hS.
pose V:=R_n R n.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose D:set V:=[set v|S (v+a)].
have [k [e [hkn [hi [heD hSpan]]]]]:=@finite_subset_independent_span R V n
  (@coordinate_basis R n) (@coordinate_basisP R n) D.
case:(eqVneq k n)=>[hEqual|hUnequal].
- subst k.
  have he:is_basis e.
    apply:(@finite_independent_basis R (finite_basis_vect (@coordinate_basisP R n)) n e)=>//.
    by rewrite finite_basis_dimension card_ord.
  have hPoints i:S (a+e i) by rewrite addrC; exact:heD i.
  have hId i:linear_id V (e i)=e i by [].
  have [b [g [r [hb [hCancel [hr hBuffer]]]]]]:=@convex_projection_section_buffer R n n
    S (linear_id V) a e e hS ha hPoints he hId.
  have hg u:g u=u:=hCancel u.
  left; exists b.
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (b:X) S)).
  exists r=>// x hx.
  have hNear:mdist (0%R:X) (x-b)<r.
    by rewrite -(@inner_translation_distance R V (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) b 0 (x-b)) add0r subrK.
  have hh:=hBuffer (x-b) hNear.
  by rewrite hg addrC subrK in hh.
- have hlt:(k<n)%N by rewrite ltn_neqAle hUnequal hkn.
  have [u hu]:=@gram_schmidt_exists R V (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) k e hi.
  have ho:=orthonormalisation_orthonormal hu.
  pose p:{linear V->V}:=GRing.Linear.clone _ _ _ _
    (orthonormal_projection (@euclidean_inner_productP R n) u) _.
  have hDet:euclidean_det p=0.
    case:(eqVneq (euclidean_det p) 0)=>[hZero|hNonzero]; first exact hZero.
    exfalso; have hInjective:injective p:=(euclidean_det_injective p).1 hNonzero.
    have hFull x:in_finite_span e x.
      have [z hz]:=euclidean_injective_surjective hInjective x.
      apply:(orthonormalisation_span hu x).2; rewrite -hz.
      exact:orthonormal_projection_in_span.
    have hBasis:=finite_basis_criterion hi hFull.
    have hSize:=finite_basis_size hBasis (@coordinate_basisP R n).
    by rewrite hSize ltnn in hlt.
  right; apply:(@euclidean_singular_affine_fixed_closure_null R n S p a hDet)=>x hx.
  have hDifference:D (x-a) by change (S ((x-a)+a)); rewrite subrK.
  apply:(@orthonormal_projection_fixed R V (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) k u ho (x-a)).
  exact:(orthonormalisation_span hu (x-a)).1 (hSpan (x-a) hDifference).
Qed.
