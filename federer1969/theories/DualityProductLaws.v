(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.
From Federer Require Import DualityMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2, final paragraph on printed page 23: the two
    displayed multiplication laws follow immediately from 1.5.1. *)
Section ProductLaws.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable omega_mu : A_m V K^o n.
Variables r s : nat.
Variable h : (r+s <= n)%N.
(** Source for [D_p_product]: Federer (1969), 1.5.2, p. 23, two displays
    before 1.5.3. In words: The duality maps turn exterior multiplication
    into the corresponding interior multiplication under the bound r+s<=n.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem D_p_product (xi : exterior_power V r) (eta : exterior_power V s) :
  D_p omega_mu h (exterior_product xi eta) =
    form_reindex (esym (subnDAC n r s))
      (right_interior (interior_degree_r h) xi (D_p omega_mu (interior_degree_s h) eta)).
Proof. exact: right_interior_associative. Qed.
Hypothesis h2 : (1+1 : K) != 0.
Variable e_mu : exterior_power V n.
(** Source for [D_upper_product]: Federer (1969), 1.5.2, p. 23, two displays
    before 1.5.3. In words: The duality maps turn exterior multiplication
    into the corresponding interior multiplication under the bound r+s<=n.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem D_upper_product (a : A_m V K^o r) (b : A_m V K^o s) :
  D_upper h2 e_mu h (form_wedge h2 (scalar_bilinear K) a b) =
    exterior_reindex (esym (subnDA r n s))
      (left_interior h2 (interior_degree_second h)
        (D_upper h2 e_mu (interior_degree_first h) a) b).
Proof. exact: left_interior_associative. Qed.
End ProductLaws.
