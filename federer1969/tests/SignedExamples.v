(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import Graded.
From FedererTests Require Import Examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CrossedGenerators.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation A := (graded_tensor_algebra V).

(** Source for [signed_cross]: Federer (1969), 1.2.2, p. 12, item (2) and
    the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Local regression example for this passage; the example
    itself is not stated in the book. *)
Example signed_cross (u v : V) :
  @graded_tensor_mul K A A true
    (tensor_inj (tensor_unit V) (tensor_generator v))
    (tensor_inj (tensor_generator u) (tensor_unit V)) =
  - tensor_inj (tensor_generator u) (tensor_generator v).
Proof.
rewrite (graded_tensor_mulE (A:=A) (B:=A) true _ _ (tensor_generator_homogeneous v)
  (tensor_generator_homogeneous u)).
change (koszul K true 1 1 *:
  tensor_inj (tensor_product (tensor_unit V) (tensor_generator u))
    (tensor_product (tensor_generator v) (tensor_unit V)) =
  - tensor_inj (tensor_generator u) (tensor_generator v)).
have hs : koszul K true 1 1 = -1 by rewrite /koszul muln1 expr1.
by rewrite (@tensor_product_unitl K V (tensor_generator u))
  (@tensor_product_unitr K V (tensor_generator v)) hs scaleN1r.
Qed.

(** Source for [ordinary_cross]: Federer (1969), 1.2.2, p. 12, item (2) and
    the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Local regression example for this passage; the example
    itself is not stated in the book. *)
Example ordinary_cross (u v : V) :
  @graded_tensor_mul K A A false
    (tensor_inj (tensor_unit V) (tensor_generator v))
    (tensor_inj (tensor_generator u) (tensor_unit V)) =
  tensor_inj (tensor_generator u) (tensor_generator v).
Proof.
rewrite (@ordinary_tensor_mulE K A A (tensor_unit V) (tensor_generator v)
  (tensor_generator u) (tensor_unit V)).
change (tensor_inj (tensor_product (tensor_unit V) (tensor_generator u))
  (tensor_product (tensor_generator v) (tensor_unit V)) =
  tensor_inj (tensor_generator u) (tensor_generator v)).
by rewrite (@tensor_product_unitl K V (tensor_generator u))
  (@tensor_product_unitr K V (tensor_generator v)).
Qed.

End CrossedGenerators.

Section DistinctProducts.
Variable K : fieldType.
Local Notation C := (Choice.clone bool _).
Local Notation V := (GRing.Lmodule.clone K (free_vector K C) _).
Local Notation A := (graded_tensor_algebra V).

(** Source for [two_generators_tensor_nonzero]: Federer (1969), 1.2.2, p.
    12, item (2) and the following explanation. In words: The signed
    tensor-product multiplication inserts (-1)^(qr) when the middle factors
    have degrees q and r; signed tensor products of anticommutative algebras
    are anticommutative. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma two_generators_tensor_nonzero :
  tensor_inj (tensor_generator (delta K false)) (tensor_generator (delta K true)) != 0.
Proof.
apply/eqP=> h.
pose f := tensor_map (tensor_degree_one V) (tensor_degree_one V).
have e := congr1 f h.
have e0 : f 0 = 0 := linear0 f.
have ei := tensor_mapE (tensor_degree_one V) (tensor_degree_one V)
  (tensor_generator (delta K false)) (tensor_generator (delta K true)).
have eg := congr2 (@tensor_inj K V V)
  (@tensor_generatorK K V (delta K false)) (@tensor_generatorK K V (delta K true)).
have ez := eq_trans (esym (eq_trans ei eg)) (eq_trans e e0).
have hn := @pure_delta_nonzero K C C false true.
by rewrite ez eqxx in hn.

Qed.

(** Source for [signed_and_ordinary_differ]: Federer (1969), 1.2.2, p. 12,
    item (2) and the following explanation. In words: The signed
    tensor-product multiplication inserts (-1)^(qr) when the middle factors
    have degrees q and r; signed tensor products of anticommutative algebras
    are anticommutative. Local regression example for this passage; the
    example itself is not stated in the book. *)
Example signed_and_ordinary_differ : (1+1 : K) != 0 ->
  @graded_tensor_mul K A A true
    (tensor_inj (tensor_unit V) (tensor_generator (delta K true)))
    (tensor_inj (tensor_generator (delta K false)) (tensor_unit V)) !=
  @graded_tensor_mul K A A false
    (tensor_inj (tensor_unit V) (tensor_generator (delta K true)))
    (tensor_inj (tensor_generator (delta K false)) (tensor_unit V)).
Proof.
move=> h2; rewrite signed_cross ordinary_cross; apply/eqP=> e.
have hz : (1+1 : K) *:
  tensor_inj (tensor_generator (delta K false)) (tensor_generator (delta K true)) = 0.
  by rewrite scalerDl !scale1r -{1}e addNr.
move/eqP: hz; by rewrite scaler_eq0 (negPf h2) orFb (negPf two_generators_tensor_nonzero).
Qed.
End DistinctProducts.
