(** Federer (1969), 1.7.3, p. 29: supporting dimension bounds for invariant
    spaces spanned by one or two vectors. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis FiniteSpans FiniteDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spanning_dimension_bound]: Federer 1.7.3,
    p. 29, supporting finite-dimensional linear algebra: a space
    spanned by m vectors has dimension at most m. The dimension
    is the length of an arbitrary basis. *)
Theorem spanning_dimension_bound (R : fieldType) (V : lmodType R)
    n (b : 'I_n -> V) (hb : is_basis b) m (e : 'I_m -> V) :
  (forall x, in_finite_span e x) -> (n <= m)%N.
Proof.
move=> hs; pose U := finite_basis_vect hb.
pose t : m.-tuple U := [tuple e i | i < m].
have hspan : (<<t>> = {:U})%VS.
  apply/vspaceP=> v; rewrite memvf; apply/idP.
  have [c ->] := hs v.
  apply: memv_suml => i _; apply: memvZ.
  apply: memv_span; apply/tnthP; exists i; by rewrite /t tnth_mktuple.
have hd := dim_span t.
by rewrite hspan dimvf /U finite_basis_dimension card_ord size_tuple in hd.
Qed.
