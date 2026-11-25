(** Federer (1969), 1.7.5, p. 32: triangular orthogonality of the original
    vectors and the Gram-Schmidt directions. This supporting consequence
    uses only the prefix-span specification. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerOrthogonality OrthonormalFamilies
  OrthonormalisationUP FinitePrefixes FiniteSpans FiniteSpanSpace ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gram_schmidt_triangular]: Federer 1.7.5,
    p. 32, the orthogonal direction at position i is orthogonal
    to every original vector at an earlier position j. *)
Theorem gram_schmidt_triangular (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (u v : 'I_n -> V) (hv : is_orthonormalisation B u v)
    (i j : 'I_n) : (j < i)%N -> B (u j) (v i) = 0.
Proof.
move=> hji.
have hi : (i <= n)%N := ltnW (ltn_ord i).
pose k : 'I_i := Ordinal hji.
have hk : widen_ord hi k = j by apply: val_inj.
have hu : in_finite_span (family_prefix hi u) (u j).
  rewrite -hk; exact: (@finite_span_generator R V i (family_prefix hi u) k).
have hw := proj1 (@orthonormalisation_prefix_span R V B n u v hv i hi (u j)) hu.
rewrite (inner_symmetric hB).
apply: (@inner_orthogonal_span R V B hB i (family_prefix hi v) (v i) (u j)) hw.
move=> a; rewrite /family_prefix (orthonormalisation_orthonormal hv).
have hn : i != widen_ord hi a.
  apply/eqP=> he; have hh := ltn_ord a.
  have ha : (i : nat) = (a : nat) := congr1 (fun x : 'I_n => (x : nat)) he.
  by rewrite -ha ltnn in hh.
by rewrite (negbTE hn).
Qed.
