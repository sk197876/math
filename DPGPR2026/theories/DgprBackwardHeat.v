(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, (3.1)-(3.3):
    the heat extensions with reversed time, [(t,x) |-> u(T - t, x)] for the
    heat extension u of (nu,f) of def:heat; blueprint dgpr_blueprint.tex,
    proof of lem:identities(div),(heat). The derivatives with respect to x
    are the convolutions with the derivatives of the heat kernel
    (lem:heat_extension(1)), and the time derivative is
    -Delta u_(T-t)(x) (DgprHeatExtensionSmooth.v). Hence the second order
    jet of the map at (t,x) with t < T is explicit, and
    H[(t,x) |-> u(T - t, x)] = 0 on Omega_T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FiniteCoordinates PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasurableFunctionUP CompleteMetricUP VectorDaniellHypotheses NormDifferentialUP NormedCurveDerivativeUP.
From DPGPR Require Import DgprParameterIntegralDifferential DgprHeatKernel DgprHeatKernelDifferential
  DgprHeatExtension DgprHeatExtensionSmooth DgprDifferentialCalculus DgprHeatJets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section BackwardHeat.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation eps := (@coordinate_basis R n).
Variable nu : set X -> \bar R.
Hypothesis hnu : is_measure nu.
Variable Z : lmodType R.
Variable NZ : Z -> R.
Hypothesis hNZ : is_real_norm NZ.
Hypothesis hZ : is_complete_metric_space (real_norm_metric_space hNZ).
Variable f : X -> Z.
Variable T : R.
Local Notation u := (@dgpr_heat_extension R n nu hnu Z NZ hNZ hZ f).
Local Notation conv := (@dgpr_convolution R n nu hnu Z NZ hNZ hZ f).

(** Source for [dgpr_backward_heat]: DPGPR 2026, (3.1)-(3.3), and
    blueprint def:heat_objects: the map [(t,x) |-> u(T - t, x)] on
    Omega_T, where u is the heat extension of (nu,f) (def:heat). *)
Definition dgpr_backward_heat (q : TX) : Z := u (T - q.1) q.2.

(** Source for [dgpr_backward_first]: blueprint lem:heat_extension(1),
    j = 1, with s = T - t: the value at v of the differential at y of
    [z |-> u(T - t, z)], the integral of D p_(T-t)(y - z)(v) f(z) d nu z. *)
Definition dgpr_backward_first (t : R) (y v : X) : Z :=
  conv (fun z => @dgpr_kernel_differential R n (T - t) z v) y.

(** Source for [dgpr_backward_second]: blueprint lem:heat_extension(1),
    j = 2, with s = T - t: the value D^2 u_(T-t)(x)(w,v), the integral of
    D^2 p_(T-t)(x - z)(w,v) f(z) d nu z; it is the differential at x of
    [y |-> D u_(T-t)(y)(w)], applied to v. *)
Definition dgpr_backward_second (t : R) (x v w : X) : Z :=
  conv (fun z => @dgpr_kernel_second R n (T - t) z w v) x.

Hypothesis hOpen : forall A : set X, @open (real_norm_metric_space hN) A -> measure_measurable nu A.
Variable m : R.
Hypothesis hmass : nu setT = m%:E.
Hypothesis hsep : is_separable_normed_space hNZ.
Hypothesis hfmeas : is_measure_measurable_function nu
  (partial_function_total (fun y => (f y : real_norm_metric_space hNZ))).
Variable M : R.
Hypothesis hfM : forall y, NZ (f y) <= M.

(** Source for [dgpr_backward_heat_jet]: DPGPR 2026, (3.3), and blueprint
    proof of lem:identities(heat): for t < T the jet of
    [(t,x) |-> u(T - t, x)] at (t,x) consists of the time derivative
    -Delta u_(T-t)(x) (lem:heat_extension(1), d/ds u = Delta u), the
    differentials of lem:heat_extension(1) for j = 1 at every point, and the
    second differential at x. *)
Theorem dgpr_backward_heat_jet (t : R) (x : X) : t < T ->
  dgpr_heat_jet NZ dgpr_backward_heat t x
    (- dgpr_laplacian_values (dgpr_backward_second t x)) (dgpr_backward_first t)
    (dgpr_backward_second t x).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
split; [|split].
- have h := dgpr_heat_extension_backward_heat hnu hZ hOpen hmass hsep hfmeas hfM x ht.
  exact: h.
- move=> y.
  have [L [hL hLv]] := dgpr_heat_extension_first hnu hZ hOpen hmass hsep hfmeas hfM y hs.
  by exists L; split.
- move=> w.
  have [L [hL hLv]] := dgpr_heat_extension_second hnu hZ hOpen hmass hsep hfmeas hfM w x hs.
  by exists L; split.
Qed.

(** Source for [dgpr_backward_heat_operator]: DPGPR 2026, (3.3), and
    blueprint lem:identities(heat): H[(t,x) |-> u(T - t, x)] = 0 on
    Omega_T, since d/dt u(T - t, x) = - Delta u_(T-t)(x). *)
Theorem dgpr_backward_heat_operator (t : R) (x : X) : t < T ->
  dgpr_heat_operator NZ dgpr_backward_heat t x 0.
Proof.
move=> ht; have h := dgpr_heat_operator_of_jet (dgpr_backward_heat_jet x ht).
by rewrite addNr in h.
Qed.

End BackwardHeat.
