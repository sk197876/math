(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3,
    (3.1), (3.2), (3.4) and (3.6): the heated objects; blueprint
    dgpr_blueprint.tex, def:heat_objects.

    Assume (S) ([dgpr_standing]). For (t,x) in Omega_T, with s = T - t,
      U(t,x) = u(s,x) for the heat extension u of (mu,1),
      W(t,x) = u(s,x) for the heat extension of (mu,X),
      R(t,x) = u(s,x) for the heat extension of (||Upsilon||,1),
      Psi(t,x) = u(s,x) for the heat extension of (||Upsilon||,dUpsilon),
      S = U + (T - t)^(1/2) R, rho(t,x) = u(s,x) for (mu0,1),
      B = S^(-1) W, eta = S^(-1) Psi, kappa = R / (2 (T - t)^(1/2) S),
      q = rho / S, zeta = grad log S_t(x), and
      I(rho_t) = integral of rho_t |grad log rho_t|^2 d L^n.
    The heat extensions are those of def:heat (DgprHeatExtension.v), with
    reversed time (DgprBackwardHeat.v). The gradients are written through
    the explicit differentials of the heat extensions: zeta(t,x) =
    S(t,x)^(-1) sum_i D S_t(x)(eps_i) eps_i, and likewise for
    grad log rho_t(x); that these are the gradients of log S_t and log rho_t
    is proved in DgprIdentities.v. All maps are total; outside Omega_T and
    where S or rho vanish their values carry no meaning. I(rho_t) is the
    upper integral of Federer 2.4.2, an extended real number.

    The operators H and H_zeta are those of DgprHeatJets.v, with
    zeta = zeta(t,x) at the point (t,x). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  CompleteMetricUP PartialFunctionUP PartialFunctionBasic MeasureUP SummableRealFunctionUP
  MeasureIntegralBounds EuclideanLebesgueDimensions ScalarNormMetricCompleteness
  SmoothFunctionSpaceUP SmoothTestSpaces.
From DPGPR Require Import DgprHeatKernel DgprHeatExtension DgprHeatJets DgprBackwardHeat DgprStanding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section HeatObjects.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Hypothesis hm : (0 < m <= n)%N.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation hHc := (@dgpr_hom_space_complete R n Y CY hCY d eY heY).
Local Notation hDc := (@dgpr_dual_space_complete R Y CY hCY d eY heY).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable T : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Hypothesis hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma.
Local Notation hmu := (dgpr_standing_mu_measure hS).
Local Notation hups := (dgpr_standing_ups_measure hS).
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation one := (fun _ : X => (1 : R^o)).

(** Source for [dgpr_heat_U]: DPGPR 2026, (3.1), P_(T-t) mu; blueprint
    def:heat_objects, U(t,x) = integral of p_(T-t)(x-y) d mu y. *)
Definition dgpr_heat_U : TX -> R := dgpr_backward_heat hmu hZ1 one T.

(** Source for [dgpr_heat_W]: DPGPR 2026, (3.1), P_(T-t) sigma (there
    called V); blueprint def:heat_objects, W(t,x) = integral of
    p_(T-t)(x-y) X(y) d mu y in Hom(R^n,Y). *)
Definition dgpr_heat_W : TX -> Hom X Y := dgpr_backward_heat hmu hHc Xf T.

(** Source for [dgpr_heat_R]: DPGPR 2026, (3.2), P_(T-t)|div sigma|;
    blueprint def:heat_objects, R(t,x) = integral of p_(T-t)(x-y)
    d ||Upsilon|| y. *)
Definition dgpr_heat_R : TX -> R := dgpr_backward_heat hups hZ1 one T.

(** Source for [dgpr_heat_Psi]: DPGPR 2026, (3.2), P_(T-t) div sigma;
    blueprint def:heat_objects, Psi(t,x) = integral of p_(T-t)(x-y)
    dUpsilon(y) d ||Upsilon|| y in Hom(Y,R). *)
Definition dgpr_heat_Psi : TX -> Hom Y R^o := dgpr_backward_heat hups hDc dups T.

(** Source for [dgpr_heat_S]: DPGPR 2026, (3.4); blueprint
    def:heat_objects, S = U + (T - t)^(1/2) R. *)
Definition dgpr_heat_S (q : TX) : R := dgpr_heat_U q + Num.sqrt (T - q.1) * dgpr_heat_R q.

(** Source for [dgpr_heat_rho]: DPGPR 2026, (3.1), P_(T-t) mu0;
    blueprint def:heat_objects, rho(t,x) = integral of p_(T-t)(x-y)
    d mu0 y. *)
Definition dgpr_heat_rho : TX -> R := dgpr_backward_heat hmu0 hZ1 one T.

(** Source for [dgpr_heat_B]: DPGPR 2026, (3.4); blueprint
    def:heat_objects, B = S^(-1) W. *)
Definition dgpr_heat_B (q : TX) : Hom X Y := (dgpr_heat_S q)^-1 *: dgpr_heat_W q.

(** Source for [dgpr_heat_eta]: DPGPR 2026, (3.4); blueprint
    def:heat_objects, eta = S^(-1) Psi. *)
Definition dgpr_heat_eta (q : TX) : Hom Y R^o := (dgpr_heat_S q)^-1 *: dgpr_heat_Psi q.

(** Source for [dgpr_heat_kappa]: DPGPR 2026, (3.4); blueprint
    def:heat_objects, kappa = R / (2 (T - t)^(1/2) S). *)
Definition dgpr_heat_kappa (q : TX) : R :=
  dgpr_heat_R q / (2 * Num.sqrt (T - q.1) * dgpr_heat_S q).

(** Source for [dgpr_heat_q]: DPGPR 2026, (3.4); blueprint
    def:heat_objects, q = rho / S. *)
Definition dgpr_heat_q (q : TX) : R := dgpr_heat_rho q / dgpr_heat_S q.

(** Source for [dgpr_heat_S_first]: the value at v of D S_t(y), from the
    differentials of U_t and R_t (lem:heat_extension(1)); supporting
    blueprint def:heat_objects, zeta = grad log S_t. *)
Definition dgpr_heat_S_first (t : R) (y v : X) : R :=
  dgpr_backward_first hmu hZ1 one T t y v + Num.sqrt (T - t) * dgpr_backward_first hups hZ1 one T t y v.

(** Source for [dgpr_heat_rho_first]: the value at v of D rho_t(y)
    (lem:heat_extension(1)); supporting blueprint def:heat_objects,
    I(rho_t). *)
Definition dgpr_heat_rho_first (t : R) (y v : X) : R := dgpr_backward_first hmu0 hZ1 one T t y v.

(** Source for [dgpr_heat_zeta]: DPGPR 2026, (3.4); blueprint
    def:heat_objects, zeta(t,x) = grad log S_t(x) =
    S(t,x)^(-1) sum_i D S_t(x)(eps_i) eps_i. *)
Definition dgpr_heat_zeta (q : TX) : X :=
  (dgpr_heat_S q)^-1 *: dgpr_gradient_values (dgpr_heat_S_first q.1 q.2).

(** Source for [dgpr_heat_grad_log_rho]: grad log rho_t(x) =
    rho(t,x)^(-1) sum_i D rho_t(x)(eps_i) eps_i; supporting blueprint
    def:heat_objects, I(rho_t). *)
Definition dgpr_heat_grad_log_rho (q : TX) : X :=
  (dgpr_heat_rho q)^-1 *: dgpr_gradient_values (dgpr_heat_rho_first q.1 q.2).

(** Source for [dgpr_fisher_information]: DPGPR 2026, section 3 (the
    Fisher information in Lemma 3.2); blueprint def:heat_objects,
    I(rho_t) = integral of rho_t |grad log rho_t|^2 d L^n, the upper
    integral of Federer 2.4.2 of a nonnegative function. *)
Definition dgpr_fisher_information (t : R) : \bar R :=
  measure_upper_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x => dgpr_heat_rho (t, x) * N (dgpr_heat_grad_log_rho (t, x)) ^+ 2)).

(** Source for [dgpr_heat_Hzeta]: DPGPR 2026, (3.6); blueprint
    def:heat_objects: H_zeta f(t,x) = H f(t,x) + 2 D f_t(x)(zeta(t,x))
    equals h. *)
Definition dgpr_heat_Hzeta (Z : lmodType R) (NZ : Z -> R) (f : TX -> Z) (t : R) (x : X) (h : Z) : Prop :=
  dgpr_heat_operator_drift NZ (dgpr_heat_zeta (t, x)) f t x h.

End HeatObjects.
