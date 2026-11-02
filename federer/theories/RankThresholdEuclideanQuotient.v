(** Federer (1969), 3.2.21, p. 257: supporting
    finite-dimensional linear algebra for selecting an orthogonal
    source block on which the differential is injective. A rank
    threshold admits an epimorphic Euclidean quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates LinearBasis
  FiniteIndependence IndependentMap BasisInterpolation LinearRetraction LinearRankAtLeast.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [rank_threshold_euclidean_quotient]: supporting
    linear-algebra step behind the choice of g in Federer
    3.2.21, p. 257. Independent differential images
    specify an injective map from R^mu; a linear retraction
    yields a quotient P for which P composed with D is onto.
    This is an existence assertion, not a chosen coordinate map. *)
Lemma rank_threshold_euclidean_quotient (R : realType) (X Y : lmodType R)
    (D : Hom X Y) mu :
  linear_rank_at_least D mu ->
  exists P : Hom Y (R_n R mu),forall y,exists x,P (D x)=y.
Proof.
move=> [e he].
pose L := basis_interpolation (@coordinate_basisP R mu) (fun i=>D (e i)).
have hImages : finite_independent (fun i=>L (@coordinate_basis R mu i)).
  have hEq : (fun i=>L (@coordinate_basis R mu i))=(fun i=>D (e i)).
    by apply: funext=> i; rewrite /L basis_interpolationE.
  by rewrite hEq.
have hLInj : injective L := @independent_basis_image_injective R (R_n R mu) Y mu
  (@coordinate_basis R mu) (@coordinate_basisP R mu) L hImages.
pose P := hom_of_linear (linear_retraction hLInj).
pose E := basis_interpolation (@coordinate_basisP R mu) e.
have hDE x : D (E x)=L x.
  apply: (basis_linear_ext (@coordinate_basisP R mu) (linear_comp (hom_as_linear D) E) L) x=> i.
  change (D (E (@coordinate_basis R mu i))=L (@coordinate_basis R mu i)).
  by rewrite /E /L !basis_interpolationE.
exists P=> y; exists (E y); rewrite hDE.
exact: linear_retractionK.
Qed.
