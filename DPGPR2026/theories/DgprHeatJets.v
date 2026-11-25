(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, (3.6):
    the heat operators H f = d/dt f + Delta f and
    H_zeta f = H f + 2 D f(zeta) on Omega_T = {(t,x) : t < T}; blueprint
    dgpr_blueprint.tex, def:heat_objects, last display.

    The operators are stated through the derivatives of f at one point
    (t,x), which are relations in Federer's library (3.1.1, 2.9.22). The
    second order jet of f at (t,x) consists of the time derivative a of
    [r |-> f(r,x)] at t, the differentials Df(y) of [z |-> f(t,z)] at every
    y of R^n, given by their values, and the values D2(v)(w) of the
    differential at x of [y |-> Df(y)(w)], applied to v. Then
    D^2 f_t(x)(v,w) = D2(v)(w) and Delta f_t(x) = sum_i D2(eps_i)(eps_i)
    for the standard basis eps of R^n (blueprint mr:notation). The value
    H f(t,x) = h is the relation [dgpr_heat_operator f t x h]; it is unique
    by [dgpr_heat_operator_unique]. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FiniteCoordinates NormDifferentialUP NormDifferentialDirectional
  NormedCurveDerivativeUP.
From DPGPR Require Import DgprDifferentialCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Jets.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation eps := (@coordinate_basis R n).
Variables (Z : lmodType R) (NZ : Z -> R).

(** Source for [dgpr_heat_jet]: blueprint mr:notation and
    def:heat_objects: a is the derivative d/dt f(t,x) of [r |-> f(r,x)] at
    t (Federer 2.9.22), Df(y) is the differential of f_t = [z |-> f(t,z)]
    at y for every y in R^n, given by its values (Federer 3.1.1), and
    D2(v)(w) is the differential at x of [y |-> Df(y)(w)], applied to v,
    that is D^2 f_t(x)(v,w) (Federer 3.1.11). *)
Definition dgpr_heat_jet (f : TX -> Z) (t : R) (x : X) (a : Z) (Df D2 : X -> X -> Z) : Prop :=
  has_normed_curve_derivative NZ (fun r => f (r, x)) t a /\
  (forall y, dgpr_differential_values NZ (fun z => f (t, z)) y (Df y)) /\
  (forall w, dgpr_differential_values NZ (fun y => Df y w) x (fun v => D2 v w)).

(** Source for [dgpr_laplacian_values]: blueprint mr:notation,
    Delta f(x) = sum_j D^2 f(x)(eps_j, eps_j), for the values D2 of the
    second differential. *)
Definition dgpr_laplacian_values (D2 : X -> X -> Z) : Z := \sum_(i < n) D2 (eps i) (eps i).

(** Source for [dgpr_heat_operator]: DPGPR 2026, (3.6), and blueprint
    def:heat_objects: H f(t,x) = d/dt f(t,x) + Delta f_t(x) equals h. *)
Definition dgpr_heat_operator (f : TX -> Z) (t : R) (x : X) (h : Z) : Prop :=
  exists a (Df D2 : X -> X -> Z), dgpr_heat_jet f t x a Df D2 /\ h = a + dgpr_laplacian_values D2.

(** Source for [dgpr_heat_operator_drift]: DPGPR 2026, (3.6), and
    blueprint def:heat_objects: H_zeta f(t,x) = H f(t,x) + 2 Df_t(x)(zeta)
    equals h, where zeta is the value zeta(t,x) of the drift. *)
Definition dgpr_heat_operator_drift (zeta : X) (f : TX -> Z) (t : R) (x : X) (h : Z) : Prop :=
  exists a (Df D2 : X -> X -> Z), dgpr_heat_jet f t x a Df D2 /\
    h = a + dgpr_laplacian_values D2 + 2 *: Df x zeta.

Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_differential_values_unique]: Federer 3.1.1, p. 209:
    the differential at a point is unique, hence so are its values. *)
Lemma dgpr_differential_values_unique (f : X -> Z) (y : X) (l l' : X -> Z) :
  dgpr_differential_values NZ f y l -> dgpr_differential_values NZ f y l' -> forall v, l v = l' v.
Proof.
move=> [L [hL hl]] [L' [hL' hl']] v.
have e := norm_differential_unique (inner_norm_real_norm (@euclidean_inner_productP R n)) hNZ hL hL'.
by rewrite -hl -hl' e.
Qed.

(** Source for [dgpr_heat_jet_unique]: Federer 2.9.22 and 3.1.1: the
    jet of f at (t,x) is determined by f. *)
Lemma dgpr_heat_jet_unique (f : TX -> Z) (t : R) (x : X) a a' (Df Df' D2 D2' : X -> X -> Z) :
  dgpr_heat_jet f t x a Df D2 -> dgpr_heat_jet f t x a' Df' D2' ->
  [/\ a = a', forall y v, Df y v = Df' y v & forall v w, D2 v w = D2' v w].
Proof.
move=> [ha [hD hD2]] [ha' [hD' hD2']].
have eD y v : Df y v = Df' y v := dgpr_differential_values_unique (hD y) (hD' y) v.
split.
- exact: (punctured_norm_limit_unique hNZ ha ha').
- exact: eD.
- move=> v w; have hw : dgpr_differential_values NZ (fun y => Df y w) x (fun v => D2' v w).
    apply: (dgpr_values_ext _ _ (hD2' w)) => [y|u] //; exact: esym (eD y w).
  exact: (dgpr_differential_values_unique (hD2 w) hw v).
Qed.

(** Source for [dgpr_heat_operator_unique]: the value H f(t,x) of
    def:heat_objects is unique. *)
Lemma dgpr_heat_operator_unique (f : TX -> Z) (t : R) (x : X) (h h' : Z) :
  dgpr_heat_operator f t x h -> dgpr_heat_operator f t x h' -> h = h'.
Proof.
move=> [a [Df [D2 [hj ->]]]] [a' [Df' [D2' [hj' ->]]]].
have [-> _ e2] := dgpr_heat_jet_unique hj hj'.
by congr (_ + _); apply: eq_bigr => i _; exact: e2.
Qed.

(** Source for [dgpr_heat_operator_drift_unique]: the value
    H_zeta f(t,x) of def:heat_objects is unique. *)
Lemma dgpr_heat_operator_drift_unique (zeta : X) (f : TX -> Z) (t : R) (x : X) (h h' : Z) :
  dgpr_heat_operator_drift zeta f t x h -> dgpr_heat_operator_drift zeta f t x h' -> h = h'.
Proof.
move=> [a [Df [D2 [hj ->]]]] [a' [Df' [D2' [hj' ->]]]].
have [-> e1 e2] := dgpr_heat_jet_unique hj hj'.
rewrite e1; congr (_ + _ + _); apply: eq_bigr => i _; exact: e2.
Qed.

(** Source for [dgpr_heat_operator_of_jet]: H f(t,x) is computed from
    any jet of f at (t,x); def:heat_objects. *)
Lemma dgpr_heat_operator_of_jet (f : TX -> Z) (t : R) (x : X) a (Df D2 : X -> X -> Z) :
  dgpr_heat_jet f t x a Df D2 -> dgpr_heat_operator f t x (a + dgpr_laplacian_values D2).
Proof. by move=> hj; exists a, Df, D2. Qed.

(** Source for [dgpr_heat_operator_drift_of_jet]: H_zeta f(t,x) is
    computed from any jet of f at (t,x); def:heat_objects. *)
Lemma dgpr_heat_operator_drift_of_jet (zeta : X) (f : TX -> Z) (t : R) (x : X) a
    (Df D2 : X -> X -> Z) :
  dgpr_heat_jet f t x a Df D2 ->
  dgpr_heat_operator_drift zeta f t x (a + dgpr_laplacian_values D2 + 2 *: Df x zeta).
Proof. by move=> hj; exists a, Df, D2. Qed.

(** Source for [dgpr_heat_jet_ext]: the jet depends only on the values
    of f; supporting def:heat_objects. *)
Lemma dgpr_heat_jet_ext (f g : TX -> Z) (t : R) (x : X) a (Df D2 : X -> X -> Z) :
  (forall q, f q = g q) -> dgpr_heat_jet f t x a Df D2 -> dgpr_heat_jet g t x a Df D2.
Proof. by move=> e; have -> : g = f by apply: funext => q; rewrite e. Qed.

End Jets.

Arguments dgpr_heat_jet {R n Z} NZ f t x a Df D2.
Arguments dgpr_laplacian_values {R n Z} D2.
Arguments dgpr_heat_operator {R n Z} NZ f t x h.
Arguments dgpr_heat_operator_drift {R n Z} NZ zeta f t x h.

Section Gradient.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation eps := (@coordinate_basis R n).

(** Source for [dgpr_gradient_values]: blueprint mr:notation, grad f(x)
    with Df(x)(v) = grad f(x) . v, computed from the values l of Df(x) in
    the standard orthonormal basis eps of R^n: grad f(x) =
    sum_i Df(x)(eps_i) eps_i (see [dgpr_gradient_valuesE]). *)
Definition dgpr_gradient_values (l : X -> R) : X := \sum_(i < n) l (eps i) *: eps i.

End Gradient.
