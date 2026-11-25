(** Federer (1969), 1.7.1, p. 28: the inductive orthonormalisation step and
    preservation of the enlarged span. The normalised residual is an
    existence witness; its orthonormality and span properties are proved
    separately. Source context are recorded in InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  OrthonormalFamilies OrthonormalProjection FiniteSpans FiniteSpanTransfer InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Extension.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : orthonormal_family B e.
Variable x : V.
Hypothesis hx : ~ in_finite_span e x.
Local Notation p := (orthonormal_projection hB e x).
Local Notation r := (x-p).
Local Notation v := (inner_normalize hB r).

(** Source for [orthonormal_extension_nonzero]: Federer
    1.7.1, p. 28, the residual in the induction step is nonzero. *)
Lemma orthonormal_extension_nonzero : r != 0.
Proof. exact: orthonormal_residual_nonzero hx. Qed.

(** Source for [orthonormal_extensionP]: Federer 1.7.1,
    p. 28, adjoining the normalised residual extends the orthonormal family. *)
Lemma orthonormal_extensionP : orthonormal_family B (ordinal_snoc e v).
Proof.
apply: (@orthonormal_snoc R V B hB n e v he).
- exact: inner_normalize_square orthonormal_extension_nonzero.
- move=> i; apply: inner_normalize_orthogonal.
  exact: (@orthonormal_residual_orthogonal R V B hB (Finite.clone 'I_n _) e he x i).
Qed.

(** Source for [orthonormal_extension_forward]: Federer
    1.7.1, p. 28, the new normalised vector is in the old enlarged span. *)
Lemma orthonormal_extension_forward : in_finite_span (ordinal_snoc e x) v.
Proof.
apply: in_finite_span_scale; apply: in_finite_span_subtract.
- exact: in_finite_span_last.
- apply: in_finite_span_snoc; exact: orthonormal_projection_in_span.
Qed.

(** Source for [orthonormal_extension_reverse]: Federer
    1.7.1, p. 28, the original new vector is in the span after
    replacing it by the normalised residual. *)
Lemma orthonormal_extension_reverse : in_finite_span (ordinal_snoc e v) x.
Proof.
have hdecomp : x = p + inner_norm hB r *: v.
  by rewrite inner_normalizeK ?orthonormal_extension_nonzero // addrC subrK.
have hs : in_finite_span (ordinal_snoc e v) (p + inner_norm hB r *: v).
  apply: in_finite_span_add.
  - apply: in_finite_span_snoc; exact: orthonormal_projection_in_span.
  - apply: in_finite_span_scale; exact: in_finite_span_last.
by rewrite -hdecomp in hs.
Qed.

(** Source for [orthonormal_extension_span]: Federer
    1.7.1, p. 28, the enlarged span is unchanged by the Gram-Schmidt step. *)
Theorem orthonormal_extension_span z :
  in_finite_span (ordinal_snoc e x) z <-> in_finite_span (ordinal_snoc e v) z.
Proof.
split.
- exact (@finite_span_snoc_transfer R V n n e e x v
    (fun y h => h) orthonormal_extension_reverse z).
- exact (@finite_span_snoc_transfer R V n n e e v x
    (fun y h => h) orthonormal_extension_forward z).
Qed.

(** Source for [orthonormal_extension_exists]: Federer
    1.7.1, p. 28, the induction step stated only by its mathematical
    properties, independently of the residual construction. *)
Theorem orthonormal_extension_exists : exists w : V,
  orthonormal_family B (ordinal_snoc e w) /\
  forall z, in_finite_span (ordinal_snoc e x) z <-> in_finite_span (ordinal_snoc e w) z.
Proof. exists v; split; [exact: orthonormal_extensionP | exact: orthonormal_extension_span]. Qed.
End Extension.
