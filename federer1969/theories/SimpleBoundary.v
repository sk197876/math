(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace SimpleZeroDegree AssociatedDimension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, first corollary: an explicit counterexample in degree
    zero, with the very same associated_space used in the dimension
    criterion. The scalar 2 is nonzero and different from 1 over every field
    of characteristic different from two, in particular R. *)
(** Source for [simple_dimension_zero_counterexample]: Federer (1969),
    1.6.1, p. 24, first of the four corollaries. In words: The printed
    corollary identifies nonzero simple m-vectors with those whose
    associated space has dimension m, and represents them as products of a
    suitable basis. Local counterexample or necessary correction to the
    printed assertion, not a claim of the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Theorem simple_dimension_zero_counterexample (K : fieldType)
  (h2 : (1+1 : K) != 0) (V : lmodType K) :
  exists (xi : exterior_power V 0) (hxi : xi != 0),
    dim (associated_space h2 hxi) = 0%N /\ ~ simple xi.
Proof.
pose xi := exterior_zeroth_inclusion V (1+1 : K^o).
have hx : xi != 0 := @scalar_mvector_nonzero K V (1+1) h2.
exists xi, hx; split.
- exact (@associated_basis_dimension K h2 V 0 xi hx 0
    (@scalar_associated_basis K V (1+1)) (@scalar_associated_basisP K V (1+1) h2)).
- apply: scalar_not_simple; apply/eqP=> h.
  have h1 : (1 : K)=0.
    apply: (addrI (1 : K)); by rewrite addr0.
  by move: (oner_neq0 K); rewrite h1 eqxx.
Qed.
