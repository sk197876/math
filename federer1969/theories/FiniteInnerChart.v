(** Federer (1969), 3.2.28, printed pp. 263–267: suitable
    Euclidean coordinates for finite inner-product ambient spaces.
    The proof chooses an orthonormal basis only locally and exposes
    existence of charts through their abstract inverse and isometry laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CoordinateProjection LinearBasis BasisInterpolation
  InnerProductUP OrthogonalMaps OrthonormalFamilies OrthonormalisationUP GramSchmidt
  OrthogonalBasisCriteria FiniteInnerChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_inner_chart_exists]: a finite-dimensional
    inner-product space is isometric to R^n, 1.7.1, p. 28,
    supporting the actual ambient identifications in Federer
    3.2.28, pp. 263–267. No globally selected chart is defined. *)
Theorem finite_inner_chart_exists (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (b:'I_n->V):
  is_basis b ->exists (e:Hom (R_n R n) V) (p:Hom V (R_n R n)),
    is_finite_inner_chart B e p.
Proof.
move=>hb.
have [v [hv hvO]]:=orthonormal_basis_exists hB hb.
have ho:=orthonormalisation_orthonormal hvO.
pose e:=basis_interpolation (@coordinate_basisP R n) v.
pose p:=basis_interpolation hv (@coordinate_basis R n).
have hLeft:cancel e p.
  apply:(basis_linear_ext (@coordinate_basisP R n)
    (linear_comp p e) (linear_id (R_n R n)))=>i.
  change (p (e (@coordinate_basis R n i))= @coordinate_basis R n i).
  by rewrite /e /p !basis_interpolationE.
have hRight:cancel p e.
  apply:(basis_linear_ext hv (linear_comp e p) (linear_id V))=>i.
  change (e (p (v i))= v i).
  by rewrite /e /p !basis_interpolationE.
have he:is_orthogonal_map (@euclidean_inner_product R n) B e.
  have hStandard:orthonormal_family (@euclidean_inner_product R n)
      (@coordinate_basis R n).
    by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
  apply:(orthogonal_map_basis_criterion (@euclidean_inner_productP R n)
    hB (@coordinate_basisP R n) hStandard)=>i j.
  by rewrite /e !basis_interpolationE ho.
exists (hom_of_linear e),(hom_of_linear p); constructor=>//.
Qed.
