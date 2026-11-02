(** Federer (1969), 1.7.5, p. 32: splitting a vector into its projection on
    the span of earlier vectors and its orthogonal residual. The spanning
    family may be dependent; its finite basis is used only to invoke the
    abstract finite-subspace splitting theorem. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthogonalSubspaceSplit OrthogonalComplement
  LinearBasis FiniteSpans FiniteSpanTransfer FiniteSpanSpace FiniteBasisCriterion
  SpanningDimension SubspaceFamilies SubspaceCarrier ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [finite_spanning_basis_exists]: Federer
    1.7.5, p. 32, supporting finite-dimensional reduction:
    any finitely spanned space has a finite basis, even if its
    given generators are dependent. *)
Lemma finite_spanning_basis_exists (R : fieldType) (V : lmodType R)
    n (e : 'I_n -> V) :
  (forall x, in_finite_span e x) -> exists k (b : 'I_k -> V), is_basis b.
Proof.
move=> hs.
have [k [b [hb hbe]]] := @finite_independent_span R V [seq e i | i <- enum 'I_n].
exists k, b; apply: finite_basis_criterion hb _ => x.
apply: (@finite_span_mono R V n k e b) (hs x) => i.
apply: hbe; apply/mapP; exists i; first exact: mem_enum.
by [].
Qed.

(** Source for [finite_family_orthogonal_split]: Federer
    1.7.5, p. 32, every vector splits into a vector in
    the span of a finite family and a vector orthogonal to that
    span. No independence or finite ambient dimension is required. *)
Theorem finite_family_orthogonal_split (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (x : V) :
  exists u w, in_finite_span e u /\
    (forall y, in_finite_span e y -> B w y = 0%R) /\ x = (u+w)%R.
Proof.
pose S := finite_span_subspace e.
pose g := subspace_family (@finite_span_generator R V n e).
have hs (v : subspace_space S) : in_finite_span g v.
  exact: (@subspace_family_spans R V S n e (@finite_span_generator R V n e) (fun _ h => h) v).
have [k [b hb]] := @finite_spanning_basis_exists R (subspace_space S) n g hs.
exact: (@finite_subspace_orthogonal_split R V B hB S k b hb x).
Qed.
