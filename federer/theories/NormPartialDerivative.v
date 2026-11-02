(** Federer (1969), 3.1.1, p. 211: coordinate partial derivatives
    and their relation to the differential. The target is an arbitrary
    normed real vector space, as in the book. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialDirectional NormedCurveDerivativeUP FiniteCoordinates
  GrassmannAbbreviations EuclideanCoordinateTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [has_norm_partial_derivative]: D_i f(a), the limit of
    the quotient obtained by changing only coordinate i, Federer 3.1.1,
    p. 211. As with the directional limit, the domain is handled by the
    interior hypothesis of the differentiability theorem below. *)
Definition has_norm_partial_derivative (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (f : R_n R n -> Y) (a : R_n R n) (i : 'I_n) (v : Y) :=
  punctured_norm_limit NY
    (fun t => t^-1 *: (f (a+t *: (@coordinate_basis R n i))-f a)) v.

(** Source for [norm_differential_partial]: Federer 3.1.1, p. 211:
    differentiability implies existence of each partial derivative, whose
    value is the differential applied to the corresponding standard vector. *)
Theorem norm_differential_partial (R : realType) n (Y : lmodType R)
    (NX : R_n R n -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (L : Hom (R_n R n) Y) :
  has_norm_differential NX NY A f a L -> forall i,
  has_norm_partial_derivative NY f a i (L (@coordinate_basis R n i)).
Proof. move=> hf i; exact: (norm_differential_directional_limit hNX hNY hf). Qed.

(** Source for [norm_partial_derivative_unique]: uniqueness of the
    partial-derivative limit used in Federer 3.1.1, p. 211. *)
Lemma norm_partial_derivative_unique (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (f : R_n R n -> Y)
    (a : R_n R n) (i : 'I_n) (u v : Y) :
  has_norm_partial_derivative NY f a i u ->
  has_norm_partial_derivative NY f a i v -> u = v.
Proof. move=> hu hv; exact: (punctured_norm_limit_unique hNY hu hv). Qed.

(** Source for [norm_differential_partial_expansion]: the displayed
    coordinate expansion of Df(a) in Federer 3.1.1, p. 211:
    Df(a)(v) is the sum of v_i D_i f(a). This also includes dimension zero. *)
Theorem norm_differential_partial_expansion (R : realType) n (Y : lmodType R)
    (NX : R_n R n -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (L : Hom (R_n R n) Y)
    (p : 'I_n -> Y) :
  has_norm_differential NX NY A f a L ->
  (forall i, has_norm_partial_derivative NY f a i (p i)) ->
  forall v, L v = \sum_i v i *: p i.
Proof.
move=> hf hp v.
rewrite -{1}(euclidean_coordinate_expansion v) linear_sum.
apply: eq_bigr=> i _; rewrite linearZ /=; congr (_ *: _).
exact: (norm_partial_derivative_unique hNY
  (@norm_differential_partial R n Y NX NY hNX hNY A f a L hf i) (hp i)).
Qed.
