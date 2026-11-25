(** Federer (1969), 1.10.5, p. 48: supporting norming functionals for the
    dual description. This is the finite-valued one-vector Hahn-Banach
    corollary of 2.4.12, p. 86. The proof uses the sealed extension
    specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP PartialLinearMap HahnBanach SeminormLineGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dominated_functional_absolute_bound]: Federer
    1.10.5, p. 48, supporting conversion of one-sided domination
    into the absolute-value bound, by evaluating at x and -x. *)
Lemma dominated_functional_absolute_bound (R : realFieldType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (f : {linear V -> R^o}) :
  (forall x, f x<=N x) -> forall x, `|f x|<=N x.
Proof.
move=> h x; rewrite ler_norml; apply/andP; split; last exact: h.
have hn := h (-x).
by rewrite linearN (real_seminorm_negate hN) lerNl in hn.
Qed.

(** Source for [seminorm_norming_functional]: Federer 1.10.5,
    p. 48, supporting dual representation and separation.
    For every vector v there exists a linear functional bounded in
    absolute value by N and taking the value N(v) at v. No
    completeness or dimension hypothesis is imposed on the vector space. *)
Theorem seminorm_norming_functional (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) v :
  exists f : {linear V -> R^o}, (forall x, `|f x|<=N x) /\ f v=N v.
Proof.
have [f [hf hb]] := seminorm_hahn_banach hN
  (seminorm_line_graph_linear hN v) (@seminorm_line_graph_dominated R V N hN v).
exists f; split.
- exact: (@dominated_functional_absolute_bound R V N hN f hb).
- exact: hf _ _ (seminorm_line_graph_norms_vector N v).
Qed.
