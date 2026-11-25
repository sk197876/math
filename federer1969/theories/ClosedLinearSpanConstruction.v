(** Private existence construction for the closed linear span supporting
    Federer (1969), 2.3.8, p. 78. Intersect all closed linear subspaces
    containing the given generators. Source context: ClosedLinearSpanUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric ClosedLinearSpanUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).
Variable D : set M.

(** Source for [closed_span_intersection]: private intersection construction
    of the supporting span in Federer 2.3.8, p. 78 *)
Definition closed_span_intersection : set M :=
  \bigcap_(W in [set W : subspace V | closed (fun y : M => W y) /\ D `<=` W])
    (fun y : M => W y).

(** Source for [closed_span_intersection_zero]: supporting zero
    law for the construction used in Federer 2.3.8, p. 78. *)
Lemma closed_span_intersection_zero : closed_span_intersection 0.
Proof. move=> W _; exact: subspace_zero. Qed.

(** Source for [closed_span_intersection_add]: supporting additive
    law for the construction used in Federer 2.3.8, p. 78. *)
Lemma closed_span_intersection_add x y : closed_span_intersection x ->
  closed_span_intersection y -> closed_span_intersection (x+y).
Proof. move=> hx hy W hW; exact: subspace_add (hx W hW) (hy W hW). Qed.

(** Source for [closed_span_intersection_scale]: supporting scalar
    law for the construction used in Federer 2.3.8, p. 78. *)
Lemma closed_span_intersection_scale a x : closed_span_intersection x ->
  closed_span_intersection (a *: x).
Proof. move=> hx W hW; exact: subspace_scale (hx W hW). Qed.

(** Source for [closed_span_subspace_witness]: private linear
    subspace witness for the supporting span in Federer 2.3.8,
    p. 78. Its public interface will expose only the specification. *)
Definition closed_span_subspace_witness : subspace V :=
  @Subspace R V closed_span_intersection closed_span_intersection_zero
    closed_span_intersection_add closed_span_intersection_scale.

(** Source for [closed_linear_span_exists]: existence of the supporting
    least closed linear subspace for Federer 2.3.8, p. 78, used. *)
Theorem closed_linear_span_exists : exists Z : subspace V, is_closed_linear_span D Z.
Proof.
exists closed_span_subspace_witness; constructor.
- apply: closed_bigI=> W [hW _]; exact hW.
- move=> x hx W [_ hW]; exact: hW.
- move=> W hc hd x hx; exact: hx W (conj hc hd).
Qed.
End Construction.
