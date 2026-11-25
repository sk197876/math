(** Federer (1969), 1.10.1, pp. 43-44: symmetric multilinear forms.
    Arbitrary fields and dimensions are allowed. Tuple contexts and the
    multilinearity predicate reuse the project's general infrastructure
    introduced for 1.4.1; symmetry replaces the alternating condition. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import AlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Forms.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation F := (GRing.Lmodule.clone K (m.-tuple V -> W) _).

(** Source for [tuple_symmetric]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: A multilinear function is symmetric when rearranging its arguments preserves its value. The permutation-of-entries formulation is equivalent to the displayed permutation-of-positions condition. *)
Definition tuple_symmetric (f : m.-tuple V -> W) : Prop :=
  forall s t : m.-tuple V, perm_eq s t -> f s = f t.
(** Source for [sform_pred]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Supporting boolean predicate combining multilinearity and symmetry. *)
Definition sform_pred (f : F) := `[< m_linear f /\ tuple_symmetric f >].

(** Source for [S_m]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: The vector space of symmetric m-linear functions from V^m to W, using an actual tuple as its domain. Degree zero will be identified with W by evaluation on the empty tuple. *)
Record S_m := SymmetricForm {
  sform_fun : m.-tuple V -> W;
  sform_proof : sform_pred sform_fun
}.
Coercion sform_fun : S_m >-> Funclass.
(** Source for [sform_rect]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Supporting eliminator for the subtype of symmetric multilinear functions. *)
Definition sform_rect (P : S_m -> Type)
    (h : forall f hf, P (@SymmetricForm f hf)) (z : S_m) : P z :=
  match z as z' return P z' with @SymmetricForm f hf => h f hf end.
HB.instance Definition _ := [isSub for sform_fun by sform_rect].
HB.instance Definition _ := [Choice of S_m by <:].

(** Source for [sform_closed]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Symmetric multilinear functions are closed under linear combinations, giving the vector space asserted in the book. *)
Lemma sform_closed : GRing.submod_closed sform_pred.
Proof.
split.
- apply/asboolP; split; last by move=> s t _.
  by move=> s t h a x y; rewrite /= scaler0 add0r.
- move=> a f g /asboolP [hf af] /asboolP [hg ag]; apply/asboolP; split.
  + move=> s t h b x y.
    change (a *: f (context_tuple s t h (b *: x + y)) + g (context_tuple s t h (b *: x + y)) =
      b *: (a *: f (context_tuple s t h x) + g (context_tuple s t h x)) +
        (a *: f (context_tuple s t h y) + g (context_tuple s t h y))).
    rewrite (hf s t h) (hg s t h) !scalerDr !scalerA addrACA.
    by rewrite [a * b]mulrC.
  + move=> s t ht; change (a *: f s + g s = a *: f t + g t).
    by rewrite (af s t ht) (ag s t ht).
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build K F sform_pred S_m sform_closed.

(** Source for [sform_multilinear]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Every symmetric form is multilinear in its actual tuple arguments. *)
Lemma sform_multilinear (f : S_m) : m_linear f.
Proof. exact: (proj1 (elimT (asboolP _) (sform_proof f))). Qed.
(** Source for [sform_tuple_symmetric]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Every symmetric form is invariant under rearranging its arguments. *)
Lemma sform_tuple_symmetric (f : S_m) : tuple_symmetric f.
Proof. exact: (proj2 (elimT (asboolP _) (sform_proof f))). Qed.
(** Source for [sform_ext]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Supporting extensionality: symmetric forms agreeing on every tuple are equal. *)
Lemma sform_ext (f g : S_m) : f =1 g -> f = g.
Proof. move=> h; apply: val_inj; exact: funext h. Qed.
(** Source for [sform_zeroE]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: The zero form is the zero function. *)
Lemma sform_zeroE t : (0 : S_m) t = 0.
Proof. by []. Qed.
(** Source for [sform_addE]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Addition of symmetric forms is pointwise. *)
Lemma sform_addE (f g : S_m) t : (f+g) t = f t + g t.
Proof. by []. Qed.
(** Source for [sform_scaleE]: Federer 1.10.1, pp. 43-44,
    opening definition. In words: Scalar multiplication of symmetric forms is pointwise. *)
Lemma sform_scaleE a (f : S_m) t : (a *: f) t = a *: f t.
Proof. by []. Qed.

End Forms.
Arguments S_m {K} V W m.
