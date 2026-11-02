(** Federer (1969), 1.7.1, p. 28: supporting projection and residual for the
    prefix-preserving orthonormalisation argument. Source context are
    recorded in InnerProductUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies Bilinear FiniteSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Projection.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable I : finType.
Variable e : I -> V.

(** Source for [orthonormal_projection]: Federer 1.7.1,
    p. 28, supporting construction for Gram-Schmidt: project x
    by summing its inner-product coordinates times the preceding vectors. *)
Definition orthonormal_projection x := \sum_i inner_coordinate hB (e i) x *: e i.

(** Source for [orthonormal_projection_linear]: Federer
    1.7.1, p. 28, supporting linearity of the projection construction. *)
Lemma orthonormal_projection_linear : linear orthonormal_projection.
Proof.
move=> a x y; rewrite /orthonormal_projection.
have hc i : inner_coordinate hB (e i) (a *: x+y) =
  a * inner_coordinate hB (e i) x + inner_coordinate hB (e i) y.
  exact: linearP.
under eq_bigr do rewrite hc scalerDl -scalerA.
by rewrite big_split scaler_sumr.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R V V *:%R
  orthonormal_projection orthonormal_projection_linear.

Hypothesis he : orthonormal_family B e.

(** Source for [orthonormal_projection_coordinate]: Federer
    1.7.1, p. 28, the projection has the same coordinates along
    the orthonormal family as the original vector. *)
Lemma orthonormal_projection_coordinate x i :
  inner_coordinate hB (e i) (orthonormal_projection x) = inner_coordinate hB (e i) x.
Proof.
exact (@orthonormal_coefficient R V B hB I e he
  (fun j => inner_coordinate hB (e j) x) i).
Qed.

(** Source for [orthonormal_projection_combination]: Federer 1.7.1, p. 28,
    the projection fixes every vector in the span of the orthonormal family. *)
Lemma orthonormal_projection_combination (c : I -> R) :
  orthonormal_projection (\sum_i c i *: e i) = \sum_i c i *: e i.
Proof.
apply: eq_bigr => i _; by rewrite (@orthonormal_coefficient R V B hB I e he c i).
Qed.

(** Source for [orthonormal_residual_orthogonal]: Federer
    1.7.1, p. 28, subtracting the projection makes the residual
    orthogonal to every preceding vector. *)
Lemma orthonormal_residual_orthogonal x i :
  B (x - orthonormal_projection x) (e i) = 0.
Proof.
rewrite -(inner_coordinateE hB) linearB orthonormal_projection_coordinate subrr.
by [].
Qed.

(** Source for [orthonormal_projection_idempotent]: Federer
    1.7.1, p. 28, applying the supporting projection twice
    gives the same projection. *)
Lemma orthonormal_projection_idempotent :
  forall x, orthonormal_projection (orthonormal_projection x) = orthonormal_projection x.
Proof. move=> x; exact: orthonormal_projection_combination. Qed.
End Projection.

Section Span.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : orthonormal_family B e.

(** Source for [orthonormal_projection_in_span]: Federer
    1.7.1, p. 28, the projection is in the span of its finite family. *)
Lemma orthonormal_projection_in_span x : in_finite_span e (orthonormal_projection hB e x).
Proof. exists (fun i => inner_coordinate hB (e i) x); by []. Qed.

(** Source for [orthonormal_projection_fixed]: Federer
    1.7.1, p. 28, any vector in the finite span is fixed. *)
Lemma orthonormal_projection_fixed x : in_finite_span e x -> orthonormal_projection hB e x = x.
Proof.
move=> [c ->]; exact (@orthonormal_projection_combination R V B hB (Finite.clone 'I_n _) e he c).
Qed.

(** Source for [orthonormal_residual_nonzero]: Federer
    1.7.1, p. 28, the next Gram-Schmidt residual is nonzero
    if the new vector is outside the preceding span. *)
Lemma orthonormal_residual_nonzero x :
  ~ in_finite_span e x -> x - orthonormal_projection hB e x != 0.
Proof.
move=> hx; apply/eqP=> hz; apply: hx.
have heq : x = orthonormal_projection hB e x by apply/eqP; rewrite -subr_eq0 hz eqxx.
rewrite heq; exact: orthonormal_projection_in_span.
Qed.
End Span.
