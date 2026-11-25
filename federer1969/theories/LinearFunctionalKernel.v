(** Federer (1969), 1.7.13, p. 37: the closed vector subspace ker(f) used
    for the continuous-functional argument. These are supporting algebraic
    and general-topological facts, without a finite-dimensional restriction.
    Source context: HilbertSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import classical_sets topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import ModuleQuotient InnerProductUP InnerMetric InnerNormedTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [linear_functional_kernel]: Federer 1.7.13,
    p. 37, the vector subspace ker(f). The subspace closure
    laws follow directly from linearity of f. *)
Definition linear_functional_kernel (R : fieldType) (V : lmodType R)
    (f : {linear V -> R^o}) : subspace V.
Proof.
apply: (@Subspace R V (fun x => f x= 0)).
- exact: linear0.
- by move=> x y hx hy; rewrite linearD hx hy addr0.
- move=> t x hx; rewrite linearZ hx.
  change (t * 0 = 0 :> R); by rewrite mulr0.
Defined.

(** Source for [linear_functional_kernel_closed]: Federer
    1.7.13, p. 37, continuity of f makes its kernel closed,
    so the preceding nearest-point theorem applies. *)
Lemma linear_functional_kernel_closed (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (f : {linear V -> R^o}) :
    continuous (fun x : inner_metric_space hB => (f x : R^o)) ->
    closed (linear_functional_kernel f : set (inner_metric_space hB)).
Proof.
move=> hf.
change (closed ((fun x : inner_metric_space hB => (f x : R^o)) @^-1` [set 0])).
apply: preimage_closed; first by move=> x _; exact: hf.
apply: compact_closed; [exact: norm_hausdorff | exact: compact_set1].
Qed.

(** Source for [linear_functional_value_one]: Federer
    1.7.13, p. 37, for nonzero f choose a with f(a)= 1.
    Scaling any vector where f is nonzero gives such a point. *)
Lemma linear_functional_value_one (R : fieldType) (V : lmodType R)
    (f : {linear V -> R^o}) v : f v != 0 -> f ((f v)^-1 *: v)= 1.
Proof.
move=> hv; rewrite linearZ.
change ((f v)^-1 * f v = 1 :> R); by rewrite mulVf.
Qed.
