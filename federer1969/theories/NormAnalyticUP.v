(** Federer (1969), 3.1.24, pp. 237–238: the
    four local analytic conditions, specified on actual domains.
    Their equivalence is a theorem to prove for Banach spaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity ContinuousMultilinearUP
  ContinuousMultilinearSealed NormHigherDifferentialUP HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Conditions.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m X Y NX NY hNX hNY).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m X Y NX NY hNX hNY).
Variables (A:set X) (f:X->Y) (a:X).

(** Source for [norm_analytic_at]: condition (1) in Federer
    3.1.24, p. 237. On a neighbourhood of a,
    f is smooth and every positive-order differential has
    norm bounded by c^m m!, with one finite real c.
    Its original domain A contains that neighbourhood. *)
Definition norm_analytic_at :=
  exists (U:set X) (c:R),U a /\ U `<=` A /\
    norm_class_all_orders hNX hNY U f /\
    forall m,(1<=m)%N -> forall x,U x -> forall z:Z m,
      has_norm_higher_differential NX ev ZN U f m x z ->
      ZN m z<=c^+m*(m`!)%:R.

(** Source for [norm_diagonal_analytic_at]: condition (2) in
    Federer 3.1.24, p. 238. The factorial-normalized
    diagonal evaluation of each positive differential is bounded
    by c^m on the closed unit ball, uniformly on U. *)
Definition norm_diagonal_analytic_at :=
  exists (U:set X) (c:R),U a /\ U `<=` A /\
    norm_class_all_orders hNX hNY U f /\
    forall m,(1<=m)%N -> forall x,U x -> forall z:Z m,
      has_norm_higher_differential NX ev ZN U f m x z ->
      forall v,NX v<=1 ->
        NY ((m`!)%:R^-1 *: ev m [ffun i=>v] z)<=c^+m.

(** Source for [norm_taylor_analytic_at]: condition (3) in
    Federer 3.1.24, p. 238. The Taylor series
    at a converges uniformly on one neighbourhood U. The
    coefficients are actual higher differentials on U, including
    order zero; no chosen total derivative outside its domain is used. *)
Definition norm_taylor_analytic_at :=
  exists U:set X,U a /\ U `<=` A /\ norm_class_all_orders hNX hNY U f /\
    exists D:forall m,Z m,
      (forall m,has_norm_higher_differential NX ev ZN U f m a (D m)) /\
      forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
        forall x,U x ->
          NY (f x-\sum_(m<N.+1) (m`!)%:R^-1 *: ev m [ffun i=>x-a] (D m))<eps.

(** Source for [norm_polynomial_analytic_at]: condition (4) in
    Federer 3.1.24, p. 238. A series of actual
    continuous homogeneous polynomial functions, one of each degree,
    converges uniformly near a. Polynomial representation is the
    abstract symmetric-form predicate of 1.10.4. *)
Definition norm_polynomial_analytic_at :=
  exists U:set X,norm_domain_interior NX U a /\ U `<=` A /\ exists P:nat->X->Y,
    (forall m,@is_homogeneous_polynomial R X Y m (P m) /\
      continuous (fun x:real_norm_metric_space hNX=>(P m x:real_norm_metric_space hNY))) /\
    forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
      forall x,U x -> NY (f x-\sum_(m<N.+1) P m (x-a))<eps.
End Conditions.

(** Source for [norm_analytic]: the definition of analytic
    function in Federer 3.1.24, p. 239: analytic
    at every point of its actual domain. *)
Definition norm_analytic (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) :=
  forall a,A a -> @norm_analytic_at R X Y NX NY hNX hNY A f a.
