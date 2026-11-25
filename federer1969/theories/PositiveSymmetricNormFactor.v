(** Federer (1969), 3.2.46, printed p. 281: the local positive
    symmetric change L obtained from 1.7.3. Its laws are specified
    before existence. All axes and factors below remain local. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates LinearBasis Hom TensorUP Bilinear FiniteBasisCriterion FiniteBasisComparison InnerProductUP InnerProductLaws InnerNorm
  OrthonormalFamilies PrincipalAxesUP PrincipalAxes PrincipalAxesDiagonal
  SymmetricEndomorphisms OrthogonalMaps PolarFactorisationUP PolarInjection
  EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_positive_symmetric_norm_factor]: the local
    symmetric automorphism L in Federer 3.2.46, p. 281, whose positive
    eigenvalues are the g(a)-lengths of its ordinary orthonormal axes,
    and whose ordinary norm is the g(a)-norm. No global frame is chosen. *)
Record is_positive_symmetric_norm_factor (R : realType) n
    (B : R_n R n -> R_n R n -> R) (hB : is_inner_product B)
    (L : {linear R_n R n -> R_n R n}) : Prop := {
  (** Source for [positive_norm_factor_symmetric]: symmetry of L,
      Federer 3.2.46, p. 281, second paragraph. *)
  positive_norm_factor_symmetric :
    is_symmetric_endomorphism (@euclidean_inner_product R n) L;
  (** Source for [positive_norm_factor_injective]: L is an
      automorphism, Federer 3.2.46, p. 281, second paragraph. *)
  positive_norm_factor_injective : injective L;
  (** Source for [positive_norm_factor_surjective]: the onto part
      of the same automorphism assertion, Federer 3.2.46, p. 281. *)
  positive_norm_factor_surjective : forall y, exists x, L x = y;
  (** Source for [positive_norm_factor_norm]: |L(v)| equals
      g(a)(v,v)^(1/2), Federer 3.2.46, p. 281, third display. *)
  positive_norm_factor_norm : forall v,
    inner_norm (@euclidean_inner_productP R n) (L v) = inner_norm hB v;
  (** Source for [positive_norm_factor_axes]: the ordinary orthonormal
      axes with positive printed eigenvalues, Federer 3.2.46, p. 281,
      second paragraph and its first two displays. *)
  positive_norm_factor_axes : exists e : 'I_n -> R_n R n,
    is_basis e /\ orthonormal_family (@euclidean_inner_product R n) e /\
      forall i, 0 < inner_norm hB (e i) /\
        L (e i) = inner_norm hB (e i) *: e i
}.

(** Source for [positive_symmetric_norm_factor_exists]: existence
    of the actual positive symmetric L, Federer 3.2.46, p. 281,
    by 1.7.3, pp. 29--30. Apply the prescribed polar factorization
    of the identity in a principal-axis basis. Its orthogonal factor
    proves the exact norm law. Every dimension, including zero, remains. *)
Theorem positive_symmetric_norm_factor_exists (R : realType) n
    (B : R_n R n -> R_n R n -> R) (hB : is_inner_product B) :
  exists L, is_positive_symmetric_norm_factor hB L.
Proof.
pose hE := @euclidean_inner_productP R n.
have [e he] := @principal_axes_exists R (R_n R n)
  (@euclidean_inner_product R n) B hE (inner_bilinear hB)
  (inner_symmetric hB) n (@coordinate_basis R n) (@coordinate_basisP R n).
have hOff i j : i != j ->
  B ((linear_id (R_n R n)) (e i)) ((linear_id (R_n R n)) (e j)) = 0.
  move=> hij; change (B (e i) (e j) = 0).
  exact: (@principal_axes_distinct R (R_n R n) (@euclidean_inner_product R n)
    B (inner_symmetric hB) n e he i j hij).
have [L [Q [hFactor [hAxes _]]]] :=
  @polar_injection_prescribed_basis R (R_n R n) (R_n R n)
    (@euclidean_inner_product R n) B hE hB n e
    (principal_axes_basis he) (principal_axes_orthonormal he)
    (@coordinate_basis R n) (finite_basis_independent (@coordinate_basisP R n))
    (linear_id (R_n R n)) hOff.
have hEq v : Q (L v) = v := injection_factor_equation hFactor v.
have hInjective : injective L.
  move=> x y h; by rewrite -(hEq x) -(hEq y) h.
have hNorm v : inner_norm hE (L v) = inner_norm hB v.
  have h := orthogonal_map_norm hE hB (injection_factor_orthogonal hFactor) (L v).
  rewrite hEq in h; exact: esym h.
exists L; constructor.
- exact: injection_factor_symmetric hFactor.
- exact hInjective.
- exact: euclidean_injective_surjective hInjective.
- exact hNorm.
- exists e; split; first exact: principal_axes_basis he.
  split; first exact: principal_axes_orthonormal he.
  move=> i; split; last exact: hAxes.
  rewrite inner_norm_gt0; apply/negP=> /eqP hi.
  have hOne := orthonormal_diagonal (principal_axes_orthonormal he) i.
  have hZero : (@euclidean_inner_product R n) (e i) (e i) = 0.
    apply/eqP; by rewrite (inner_self_eq0 hE) hi eqxx.
  rewrite hZero in hOne.
  have h01 : (0 : R) < 1 := ltr01.
  by rewrite -hOne ltxx in h01.
Qed.
