(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace AbsentBasisProducts InitialIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: in the Grassmann expansion, all coefficients vanish
    unless lambda contains the initial k indices. A nonzero coefficient
    then proves k<=m. This is exactly the basis argument in the book. *)
Section Coordinates.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n m k : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Variable hkn : (k <= n)%N.
Variable xi : exterior_power V m.
Hypothesis hT : forall i : 'I_k, FedererSimple.T xi (e (widen_ord hkn i)).
Local Notation initial := (Lambda_initial hkn).
Local Notation c := (xi_lambda h2 omega xi).
(** Source for [initial_coordinate_zero]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem initial_coordinate_zero (lambda : Lambda n m) :
  ~~ (Lambda_set initial \subset Lambda_set lambda) -> c lambda = 0.
Proof.
move/subsetPn=> [i hi hn].
have hik : (i < k)%N by move: hi; rewrite initial_set_mem.
have hie : widen_ord hkn (Ordinal hik) = i by apply: val_inj.
have ht := hT (Ordinal hik); rewrite hie in ht.
exact (@associated_coordinate_zero K h2 V n m e omega he hdual xi i lambda ht hn).
Qed.
(** Source for [nonzero_Grassmann_coordinate]: Federer (1969), 1.6.1, p. 23,
    last paragraph, basis extension and the Grassmann-coordinate argument.
    In words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma nonzero_Grassmann_coordinate : xi != 0 -> exists lambda, c lambda != 0.
Proof.
move=> hxi; have [h|h] := pselect (exists lambda, c lambda != 0); first exact: h.
have hc lambda : c lambda = 0.
  apply/eqP; apply/negPn/negP=> hn; apply: h; by exists lambda.
have hz : xi = 0.
  rewrite {1}(@vector_Grassmann_expansion K h2 V n m e omega he hdual xi).
  apply: big1 => lambda _; by rewrite hc scale0r.
by move: hxi; rewrite hz eqxx.
Qed.
(** Source for [initial_dimension_bound]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem initial_dimension_bound : xi != 0 -> (k <= m)%N.
Proof.
move/nonzero_Grassmann_coordinate=> [lambda hc].
have hsub : Lambda_set initial \subset Lambda_set lambda.
  apply/negPn/negP=> hn; have hz := initial_coordinate_zero hn.
  by move: hc; rewrite hz eqxx.
exact: complementary_degrees hsub.
Qed.
(** Source for [initial_Grassmann_expansion]: Federer (1969), 1.6.1, p. 23,
    last paragraph, basis extension and the Grassmann-coordinate argument.
    In words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem initial_Grassmann_expansion :
  xi = \sum_(lambda : Lambda n m | Lambda_set initial \subset Lambda_set lambda)
    c lambda *: e_lambda e (val lambda).
Proof.
rewrite {1}(@vector_Grassmann_expansion K h2 V n m e omega he hdual xi)
  (bigID (fun lambda : Lambda n m => Lambda_set initial \subset Lambda_set lambda)) /=.
have hz : (\sum_(lambda : Lambda n m | ~~ (Lambda_set initial \subset Lambda_set lambda))
    c lambda *: e_lambda e (val lambda)) = 0.
  apply: big1 => lambda hn; by rewrite (initial_coordinate_zero hn) scale0r.
by rewrite hz addr0.
Qed.
End Coordinates.
