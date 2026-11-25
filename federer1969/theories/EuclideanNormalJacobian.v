(** Supporting the affine slicing calculation in Federer (1969), 2.10.16, p.
    178: the normal Jacobian is the norm of the top exterior power of the
    adjoint. Its polar projection factorisation has Jacobian equal to the
    absolute determinant of its symmetric factor. This follows from
    1.7.3–1.7.6, pp. 30–34, and supports the determinant coordinate change
    of 2.7.16, pp. 134–135. All norms and adjoints use the existing abstract
    interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps InnerProductUP InnerNorm InnerNormalization InnerExterior InnerExteriorPositivity
  ExteriorNorm ExteriorNormNaturality ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorDeterminant
  ExteriorOperatorNorm TopExteriorNorm LinearBasis TensorUP AdjointUP Adjoint AdjointLaws
  PolarFactorisationUP OperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_normal_jacobian]: supporting normal
    Jacobian in the coordinate calculation for 2.10.16,
    p. 178. It is defined through the existing abstract
    exterior operator norm of 1.7.6, pp. 33–34, rather
    than through a particular matrix determinant construction. *)
Definition euclidean_normal_jacobian (R : realType) (n m : nat)
    (F : {linear R_n R n -> R_n R m}) :=
  exterior_operator_norm (euclidean_two_nonzero R)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) (@coordinate_basisP R m)
    (inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F) m.
Arguments euclidean_normal_jacobian {R n m} F.

(** Source for [euclidean_normal_jacobian_nonnegative]: supporting
    nonnegative normal Jacobian for 2.10.16, p. 178,
    from the existing norm laws of 1.7.6, p. 33. *)
Lemma euclidean_normal_jacobian_nonnegative (R : realType) (n m : nat)
    (F : {linear R_n R n -> R_n R m}) : 0<=euclidean_normal_jacobian F.
Proof.
rewrite /euclidean_normal_jacobian /exterior_operator_norm.
exact: linear_operator_norm_nonnegative.
Qed.

(** Source for [euclidean_normal_jacobian_unit_value]: supporting
    evaluation law for 2.10.16, p. 178. The top-degree
    operator norm equals its value on any unit top vector,
    by 1.7.6, p. 34; this includes degree zero. *)
Lemma euclidean_normal_jacobian_unit_value (R : realType) (n m : nat)
    (F : {linear R_n R n -> R_n R m}) (w : exterior_power (R_n R m) m) :
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) w= 1 ->
  euclidean_normal_jacobian F=
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (exterior_power_map (inner_adjoint (@euclidean_inner_productP R n)
        (@euclidean_inner_productP R m) (@coordinate_basisP R n) F) m w).
Proof. move=> hw; exact: top_exterior_operator_unit_value hw. Qed.

(** Source for [projection_factor_normal_jacobian]: supporting
    determinant factor for the normal-coordinate calculation
    in 2.10.16, p. 178. If F=K composed with p is
    the proved symmetric/projection factorisation of 1.7.3,
    p. 30, then the normal Jacobian is the absolute
    determinant of K, also when K is singular. *)
Theorem projection_factor_normal_jacobian (R : realType) (n m : nat)
    (F : {linear R_n R n -> R_n R m}) (K : {linear R_n R m -> R_n R m})
    (p : {linear R_n R n -> R_n R m}) :
  is_projection_factorisation (@euclidean_inner_product R n) (@euclidean_inner_product R m) F K p ->
  euclidean_normal_jacobian F=`|euclidean_det K|.
Proof.
move=> [hsym [u [hu hpu]] heq].
pose h2 := euclidean_two_nonzero R.
pose hBn := @euclidean_inner_productP R n.
pose hBm := @euclidean_inner_productP R m.
have hpu' := @adjoint_reverse R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n) hBm hBn u p hpu.
pose a := inner_adjoint hBn hBm (@coordinate_basisP R n) F.
have ha : is_adjoint (@euclidean_inner_product R n) (@euclidean_inner_product R m) F a.
  exact: inner_adjointP.
have hcomp : is_adjoint (@euclidean_inner_product R n) (@euclidean_inner_product R m)
    F (linear_comp u K).
  move=> x y; change (euclidean_inner_product x (u (K y))=euclidean_inner_product (F x) y).
  by rewrite hpu' -hsym heq.
have hae := adjoint_unique hBn ha hcomp.
pose hE := @exterior_inner_productP R h2 (R_n R m) (@euclidean_inner_product R m) hBm m.
pose w := inner_normalize hE (@top_vector R m (R_n R m) (@coordinate_basis R m)).
have hw : exterior_norm h2 hBm w= 1.
  apply: inner_normalize_norm.
  exact (@top_vector_nonzero R h2 m (R_n R m) (@coordinate_basis R m) (@coordinate_basisP R m)).
rewrite (euclidean_normal_jacobian_unit_value F hw).
have hext : exterior_power_map a m w=exterior_power_map (linear_comp u K) m w.
  apply: exterior_power_map_ext=> x; exact: hae.
change (exterior_norm h2 hBn (exterior_power_map a m w)=`|euclidean_det K|).
rewrite hext -exterior_power_map_composition
  (@exterior_norm_orthogonal_natural R h2 (R_n R m) (R_n R n) _ _ hBm hBn u hu m _)
  (@detE R h2 m (R_n R m) (@coordinate_basis R m) (@coordinate_basisP R m) K w)
  exterior_norm_scale hw mulr1.
by [].
Qed.
