(** Federer (1969), 2.7.4, printed p. 123, proof of the theorem: "Whenever u
    in K(X)+ and 0 <> v in K(X)+ we let C(u,v) be the set of all maps xi: G
    -> {t: 0 <= t < oo} for which {g: xi(g) > 0} is finite and u <= sum_{g
    in G} xi(g) . (v o A_g), and we define the so-called Haar ratio (u:v) =
    inf{sum_G xi: xi in C(u,v)}." The sums over G are finitely supported
    sums (fsbigop of MathComp classical), the inequality between functions
    is function_le of 2.5.1, and K(X)+ is positive_function_lattice of the
    lattice K(X) of 2.5.13. The Haar ratio is specified by its infimum laws:
    r is a lower bound of the sums sum_G xi with xi in C(u,v), and every
    lower bound is at most r. A Haar ratio function assigns such an infimum
    to every u in K(X)+ and every nonzero v in K(X)+. The existence of Haar
    ratios and their properties are proved in HaarRatioLaws.v. Only the
    choice structure of G is used here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  cardinality fsbigop topology.
From Federer Require Import FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HaarRatio.
Variable R : realType.
Variable G : choiceType.
Variable X : topologicalType.
Variable A : G -> X -> X.

(** Source for [group_sum]: the sum "sum_G xi" of Federer 2.7.4,
    p. 123, of a map xi: G -> R for which {g: xi(g) > 0} is finite.
    Definition by the finitely supported sum over G. *)
Definition group_sum (xi : G -> R) : R := \sum_(g \in [set: G]) xi g.

(** Source for [haar_cover]: "C(u,v) be the set of all maps
    xi: G -> {t: 0 <= t < oo} for which {g: xi(g) > 0} is finite and
    u <= sum_{g in G} xi(g) . (v o A_g)", Federer 2.7.4, p. 123. Direct
    definition. *)
Definition haar_cover (u v : X -> R) : set (G -> R) :=
  [set xi | [/\ forall g, 0 <= xi g, finite_set [set g | 0 < xi g] &
    function_le u (fun x => \sum_(g \in [set: G]) xi g * v (A g x))]].

(** Source for [is_haar_ratio]: "(u:v) = inf{sum_G xi: xi in
    C(u,v)}", Federer 2.7.4, p. 123. Definition of the infimum by its
    laws: r is a lower bound of the sums, and every lower bound is at
    most r. *)
Definition is_haar_ratio (u v : X -> R) (r : R) : Prop :=
  (forall xi, haar_cover u v xi -> r <= group_sum xi) /\
  (forall b, (forall xi, haar_cover u v xi -> b <= group_sum xi) -> b <= r).

(** Source for [is_haar_ratio_function]: "Whenever u in K(X)+ and
    0 <> v in K(X)+ ... we define the so-called Haar ratio (u:v)",
    Federer 2.7.4, p. 123. Definition: rho u v is the Haar ratio (u:v)
    whenever u in K(X)+ and v is a nonzero member of K(X)+. *)
Definition is_haar_ratio_function (rho : (X -> R) -> (X -> R) -> R) : Prop :=
  forall u v, positive_function_lattice (@compactly_supported_continuous_functions R X) u ->
    positive_function_lattice (@compactly_supported_continuous_functions R X) v ->
    (exists x, v x <> 0) -> is_haar_ratio u v (rho u v).

End HaarRatio.
