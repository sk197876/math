(** Federer (1969), 3.2.38, p. 275: the top intrinsic volume
    of an affine image is its actual source Jacobian times cube volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness LinearBasis FiniteBasisComparison FiniteIndependence IndependentMap
  OrthogonalMaps OrthogonalEuclidean ProjectedVolumeGauge PolarFactorisationUP PolarInjection
  EuclideanLinearMaps ExteriorDeterminant EuclideanLinearJacobian LinearJacobianPrecomposition LinearJacobianSandwich.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_linear_intrinsic_factor_exists]: supporting
    zeta^m(g(K))=J_m f(a)L^m(K) in Federer 3.2.38, p. 275.
    The earlier opaque polar theorem 1.7.3 factors every actual linear
    map through an orthogonal injection and a source endomorphism.
    Target capacity follows from m<=n, including singular maps and
    zero source dimension. The actual Jacobian is the absolute
    determinant of the source factor; no invertibility is assumed. *)
Lemma euclidean_linear_intrinsic_factor_exists (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  (m<=n)%N ->exists (K:{linear R_n R m->R_n R m}) (O:{linear R_n R m->R_n R n}),
    is_injection_factorisation (@euclidean_inner_product R m) (@euclidean_inner_product R n)
      (hom_as_linear D) K O /\euclidean_linear_jacobian m D=`|euclidean_det K|.
Proof.
move=>hmn.
have [p [F [hF hAdj]]]:=@euclidean_projection_exists R n m hmn.
have hFInjective:=orthogonal_map_injective (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) hF.
have hCapacity:=finite_independent_map hFInjective (finite_basis_independent (@coordinate_basisP R m)).
have [K [O hFactor]]:=@polar_injection_factorisation_exists R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  (fun i=>F (@coordinate_basis R m i)) hCapacity (hom_as_linear D).
exists K,O; split; first exact hFactor.
pose OH:=hom_of_linear O.
pose KH:=hom_of_linear K.
have hLength v:inner_norm (@euclidean_inner_productP R n) (OH v)=
    inner_norm (@euclidean_inner_productP R m) v.
  exact:(orthogonal_map_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (injection_factor_orthogonal hFactor) v).
have hLower v:1*inner_norm (@euclidean_inner_productP R m) v<=
    inner_norm (@euclidean_inner_productP R n) (OH v) by rewrite hLength mul1r.
have hUpper v:inner_norm (@euclidean_inner_productP R n) (OH v)<=
    1*inner_norm (@euclidean_inner_productP R m) v by rewrite hLength mul1r.
have [hJl hJu]:=euclidean_top_jacobian_sandwich (@ler01 R) (@ler01 R) hLower hUpper.
have hJOne:euclidean_linear_jacobian m OH= 1.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - by move:hJu; rewrite expr1n.
  - by move:hJl; rewrite expr1n.
have hComposition:hom_comp OH KH=D.
  apply:hom_ext=>x; exact:(injection_factor_equation hFactor x).
have hJacobian:=euclidean_top_jacobian_precompose OH KH.
rewrite hComposition hJOne mulr1 in hJacobian.
rewrite hJacobian; congr (`|_|).
apply:det_ext=>x; by rewrite hom_as_linearE /KH hom_of_linearE.
Qed.
