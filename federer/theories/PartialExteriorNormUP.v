(** Federer (1969), 3.2.20, p. 256: the exterior norm of
    the actual partial approximate differential. Specify bounds on its
    decomposable exterior words before proving existence. On an
    m-dimensional tangent plane, the top-degree specification is the
    ordinary operator norm of 1.7.6, pp. 33–34. No off-domain values
    of a linear representative enter these laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps FiniteExteriorPowers
  PartialFunctionUP InnerNorm InnerExterior ExteriorGrading ExteriorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_partial_exterior_bound]: supporting intrinsic reading
    of the exterior-power norm in Federer 3.2.20, p. 256,
    using the unit-ball bound of 1.7.6, p. 33. Test actual
    q-tuples in the partial graph and their exterior products. This
    definition does not choose ambient extensions or assign values to
    the partial function outside its domain. *)
Definition is_partial_exterior_bound (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k)) (J : R) : Prop :=
  forall (v : 'I_q -> R_n R n) (w : 'I_q -> R_n R k),
    (forall i, partial_function_graph d (v i) (w i)) ->
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (e_lambda v (ord_tuple q))<=1 ->
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R k)
      (e_lambda w (ord_tuple q))<=J.

(** Source for [is_partial_exterior_norm]: the supremum norm used in
    Federer 3.2.20, p. 256, with the unit-ball convention of
    1.7.6, p. 33. Its independent laws specify the least
    nonnegative bound on actual exterior words. On a tangent vector
    space this is compared with the usual exterior operator norm;
    for an exceptional non-linear cone it keeps only the actual
    partial graph rather than using arbitrary off-cone values. Existence
    is a separate theorem for partial maps having a linear representative. *)
Record is_partial_exterior_norm (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k)) (J : R) : Prop := {
  (** Source for [partial_exterior_norm_nonnegative]: nonnegative norm
      in Federer 3.2.20, p. 256, with the empty nonnegative
      supremum interpreted as zero in positive exterior degree. *)
  partial_exterior_norm_nonnegative : 0<=J;
  (** Source for [partial_exterior_norm_bound]: unit exterior-word
      bound supporting the norm in Federer 3.2.20, p. 256. *)
  partial_exterior_norm_bound : is_partial_exterior_bound q d J;
  (** Source for [partial_exterior_norm_least]: least upper bound
      law supporting the norm in Federer 3.2.20, p. 256;
      no attainment on a possibly non-linear cone is postulated. *)
  partial_exterior_norm_least : forall L : R, 0<=L -> is_partial_exterior_bound q d L -> J<=L
}.
