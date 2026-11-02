(** Private existence proof of the separable closed span used in Federer
    (1969), 2.3.8, p. 78, and 2.3.9, pp. 79–80. Source context:
    ClosedLinearSpanUP.v. The closure of a countable rational hull is a real
    linear subspace; minimality identifies it with any object satisfying the
    abstract closed-span specification. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric ClosedLinearSpanUP
  CountableRationalHullConstruction NormClosureLaws MetricCountableClosureSeparability MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).
Variable D : set M.

(** Source for [rational_hull_in_subspace]: supporting minimality
    of the countable hull for Federer 2.3.8, p. 78;
    every real subspace containing the generators contains the hull. *)
Lemma rational_hull_in_subspace (W : subspace V) : D `<=` W ->
  @rational_hull R V D `<=` W.
Proof.
move=> hd x [n _ hx]; elim: n x hx=> [x [->|hx]|n ih x [[hx|hx]|hx]] /=.
- exact: subspace_zero.
- exact: hd.
- exact: ih.
- have [[a b] [ha hb] <-] := hx; exact: subspace_add (ih a ha) (ih b hb).
- have [[q a] [_ ha] <-] := hx; exact: subspace_scale (ih a ha).
Qed.

(** Source for [rational_hull_closed_subspace]: private subspace
    witness for Federer 2.3.8, p. 78. Additive closure
    follows by continuity of translations; rational-scalar closure
    extends to real scalars by rational density. *)
Definition rational_hull_closed_subspace : subspace V :=
  @Subspace R V (closure (rational_hull D))
    (@subset_closure M _ 0 (@rational_hull_zero R V D))
    (@norm_closure_add_stable R V N hN _ (@rational_hull_add R V D))
    (@norm_closure_rational_scale_stable R V N hN _ (@rational_hull_scale R V D)).

(** Source for [rational_hull_closed_span_laws]: verification of
    the closed-span universal property for the supporting witness
    in Federer 2.3.8, p. 78. *)
Lemma rational_hull_closed_span_laws : is_closed_linear_span D rational_hull_closed_subspace.
Proof.
constructor.
- exact: closed_closure.
- move=> x hx; apply: subset_closure; exact: rational_hull_contains.
- move=> W hc hd x hx; apply: hc.
  exact: (@closureS M _ (fun y : M => W y) (rational_hull_in_subspace hd) x hx).
Qed.

(** Source for [closed_linear_span_countable_separable_exists]: supporting
    countable closed-span separability for Federer 2.3.8, p. 78 The
    statement is about every abstract closed-span witness. *)
Theorem closed_linear_span_countable_separable_exists (Z : subspace V) :
  countable D -> is_closed_linear_span D Z ->
  exists E : set (metric_subset (fun y : M => Z y)), countable E /\ dense E.
Proof.
move=> hd hz.
have he : (fun y : M => Z y) = closure (rational_hull D).
  apply: funext=> y; apply: propext.
  exact: (closed_linear_span_unique_membership hz rational_hull_closed_span_laws y).
rewrite he; apply: countable_metric_closure_separable.
exact: rational_hull_countable.
Qed.
End Construction.
