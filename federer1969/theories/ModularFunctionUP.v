(** Federer (1969), 2.7.8, printed p. 126: "Theorem. There exists a
    continuous positive real valued function Delta_G with the following
    properties: (1) Every left Haar integral of G is right Delta_G
    covariant. (2) Every right Haar integral of G is left Delta_G covariant.
    (3) If lambda is a left Haar integral of G, then lambda_x[u(x^{-1})
    Delta_G(x^{-1})] = lambda(u) whenever u in K(G). (4) If mu is a right
    Haar integral of G, then mu_x[u(x^{-1}) Delta_G(x)] = mu(u) whenever u
    in K(G). Moreover Delta_G is uniquely characterized by each of these
    properties; it is called the modular function of G." This file specifies
    each of the four properties of a function D: G -> R by a predicate, and
    the modular function by the predicate is_modular_function: D is
    continuous, positive and has the properties (1)-(4). The covariant
    integrals and Haar integrals are those of HaarIntegralUP.v (2.7.2, p.
    122); lambda_x[u(x^{-1}) D(x^{-1})] is lambda applied to x |-> u(x^{-1})
    D(x^{-1}). Existence and the four uniqueness statements are proved in
    ModularFunction.v; later results use only the predicate. The local
    erratum has no entry for p. 126. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ModularFunctionProperties.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G).
Local Notation K := (@compactly_supported_continuous_functions R G).

(** Source for [left_haar_right_covariant]: property (1) of Federer
    2.7.8, p. 126, "Every left Haar integral of G is right Delta_G
    covariant", for a function D in place of Delta_G. Definition. *)
Definition left_haar_right_covariant (D : G -> R) : Prop :=
  forall lambda, is_left_haar_integral mul lambda -> is_right_covariant_integral mul inv D lambda.

(** Source for [right_haar_left_covariant]: property (2) of Federer
    2.7.8, p. 126, "Every right Haar integral of G is left Delta_G
    covariant", for a function D in place of Delta_G. Definition. *)
Definition right_haar_left_covariant (D : G -> R) : Prop :=
  forall mu, is_right_haar_integral mul inv mu -> is_left_covariant_integral mul D mu.

(** Source for [left_haar_inversion_identity]: property (3) of Federer
    2.7.8, p. 126, "If lambda is a left Haar integral of G, then
    lambda_x[u(x^{-1}) Delta_G(x^{-1})] = lambda(u) whenever
    u in K(G)", for a function D in place of Delta_G. Definition. *)
Definition left_haar_inversion_identity (D : G -> R) : Prop :=
  forall lambda, is_left_haar_integral mul lambda ->
    forall u, K u -> lambda (fun x => u (inv x) * D (inv x)) = lambda u.

(** Source for [right_haar_inversion_identity]: property (4) of
    Federer 2.7.8, p. 126, "If mu is a right Haar integral of G, then
    mu_x[u(x^{-1}) Delta_G(x)] = mu(u) whenever u in K(G)", for a
    function D in place of Delta_G. Definition. *)
Definition right_haar_inversion_identity (D : G -> R) : Prop :=
  forall mu, is_right_haar_integral mul inv mu ->
    forall u, K u -> mu (fun x => u (inv x) * D x) = mu u.

(** Source for [is_modular_function]: Federer 2.7.8, p. 126, "a
    continuous positive real valued function Delta_G with the following
    properties: (1) ... (4) ... it is called the modular function of
    G". Definition by the properties of the theorem. *)
Record is_modular_function (D : G -> R) : Prop := {
  (** Source for [modular_function_continuous]: "continuous", Federer
      2.7.8, p. 126. *)
  modular_function_continuous : continuous (D : G -> real_line_metric R);
  (** Source for [modular_function_positive]: "positive real valued",
      Federer 2.7.8, p. 126. *)
  modular_function_positive : forall g, 0 < D g;
  (** Source for [modular_function_left_haar]: property (1) of Federer
      2.7.8, p. 126. *)
  modular_function_left_haar : left_haar_right_covariant D;
  (** Source for [modular_function_right_haar]: property (2) of
      Federer 2.7.8, p. 126. *)
  modular_function_right_haar : right_haar_left_covariant D;
  (** Source for [modular_function_left_inversion]: property (3) of
      Federer 2.7.8, p. 126. *)
  modular_function_left_inversion : left_haar_inversion_identity D;
  (** Source for [modular_function_right_inversion]: property (4) of
      Federer 2.7.8, p. 126. *)
  modular_function_right_inversion : right_haar_inversion_identity D
}.

End ModularFunctionProperties.
