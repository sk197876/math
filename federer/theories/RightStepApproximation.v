(** Federer (1969), 2.9.24, p. 169: the uniform step function f_n uses f at
    the right endpoint of each cell (t_j,t_(j+1)]. Our index n starts with
    n+1 cells. The finite step maps are already sealed; these laws use their
    abstract specification. The local Federer erratum has no entry for this
    step. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP BorelRegularMeasureUP
  MeasurableFunctionUP PartialFunctionBasic SummableRealFunctionUP
  StieltjesSums StieltjesIntegral StieltjesIntegrationByParts StieltjesSubstitution
  TaggedStepFunction TaggedStepMeasurability TaggedStepBounds TaggedStepConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_right_step_approximation]: direct f_n
    in Federer 2.9.24, p. 169, with n+1 cells and
    zero outside the left-open, right-closed interval. *)
Definition uniform_right_step_approximation (R : realType) (f : R -> R)
    (a b : R) (n : nat) :=
  tagged_step_function f (uniform_right_tagged a ((b-a)/n.+1%:R) n.+1).

(** Source for [uniform_right_step_integrand_measurable]: supporting
    measurability of f_n in Federer 2.9.24, p. 169.
    The finite approximation needs no regularity hypothesis on f. *)
Lemma uniform_right_step_integrand_measurable (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (f : R -> R) (a b : R) (n : nat) :
  is_measure_measurable_function mu (real_total_integrand (uniform_right_step_approximation f a b n)).
Proof. exact: tagged_step_integrand_measurable. Qed.

(** Source for [uniform_right_step_bound]: supporting uniform bound on f_n
    in Federer 2.9.24, p. 169 A bound for f on [a,b] also bounds every
    approximation on the entire line. *)
Lemma uniform_right_step_bound (R : realType) (f : R -> R) (a b M : R) :
  a<=b -> 0<=M -> (forall x : R, a<=x -> x<=b -> `|f x|<=M) ->
  forall (n : nat) (x : R), `|uniform_right_step_approximation f a b n x|<=M.
Proof.
move=> hab hM hf n x.
have hw := @uniform_right_tagged_is R a b n hab.
apply: (@tagged_step_function_value_bound R f _ M hM) => t ht.
have /andP[hat htb] := @tagged_partition_mem_bounds R a b _ t hw ht.
exact: hf t hat htb.
Qed.

(** Source for [uniform_right_step_pointwise_limit]: supporting
    convergence at every continuity point in Federer 2.9.24,
    p. 169. The whole sequence of uniform meshes tends
    to zero; both interior points and the right endpoint qualify. *)
Lemma uniform_right_step_pointwise_limit (R : realType) (f : R -> R)
    (a b x : R) : a<=b -> a<x -> x<=b ->
  (f : real_line_metric R -> real_line_metric R) @ (x : real_line_metric R) -->
    (f x : real_line_metric R) ->
  forall e : R, 0<e -> exists N : nat, forall n : nat, (N<=n)%N ->
    `|uniform_right_step_approximation f a b n x-f x|<e.
Proof.
move=> hab hax hxb hc e he.
have [d [hd herr]] := @tagged_step_continuity_error R f x e hc he.
have [N hN] := @uniform_mesh_small R a b d hab hd.
exists N=> n hn.
have hw := @uniform_right_tagged_is R a b n hab.
have hm := @uniform_right_tagged_mesh R a ((b-a)/n.+1%:R) d n.+1 (hN n hn).
apply: (herr _ hw.1 hw.2.1 hm).
- by rewrite uniform_right_tagged_head.
- have hend : a+n.+1%:R*((b-a)/n.+1%:R)=b.
    by rewrite mulrC mulfVK ?pnatr_eq0 // addrC subrK.
  by rewrite uniform_right_tagged_last hend.
Qed.
