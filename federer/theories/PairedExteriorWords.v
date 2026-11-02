(** Federer (1969), 1.6.5, p. 26: replacement of the common factors P(e_j),
    Q(e_j) by a_j, b_j in the displayed computation. Supporting
    ordered-product laws make this step precise for an arbitrary number of
    common factors, including zero. The proof uses only the exterior
    algebra's associative, bilinear and anticommutative laws. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ProductSpaceMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_word_double_cons]: Federer 1.6.5, p. 26,
    reordering the two blocks of product factors. Supporting identity:
    moving the first factor of the second block past the tail of the
    first block produces the sign given by that tail's length. *)
Lemma exterior_word_double_cons (K : fieldType) (W : lmodType K)
  (a b : W) (s t : seq W) :
  wedge (exterior_word (a :: s)) (exterior_word (b :: t)) =
    (-1 : K)^+(size s) *:
      wedge (wedge (exterior_generator a) (exterior_generator b))
        (wedge (exterior_word s) (exterior_word t)).
Proof.
have hs : wedge (exterior_word s) (exterior_generator b) =
    (-1 : K)^+(size s) *: wedge (exterior_generator b) (exterior_word s).
  have h := exterior_words_anticommutative s [:: b].
  by rewrite /= muln1 exterior_word_cons exterior_word_nil wedge_unitr in h.
rewrite !exterior_word_cons -wedge_assoc
  (wedge_assoc (exterior_word s)) hs
  (bilZl (wedge_bilinear W)) (bilZr (wedge_bilinear W))
  -wedge_assoc wedge_assoc.
by [].
Qed.

(** Source for [paired_exterior_words_replace]: Federer 1.6.5,
    p. 26, replacement P(e_j) wedge Q(e_j)=a_j wedge b_j.
    Supporting generalisation: equality of each paired two-vector
    implies equality of the corresponding two ordered blocks.
    No independence assumption is needed. *)
Theorem paired_exterior_words_replace (K : fieldType) (U : Type)
  (W : lmodType K) (P Q A B : U -> W)
  (h : forall v, wedge (exterior_generator (P v)) (exterior_generator (Q v)) =
    wedge (exterior_generator (A v)) (exterior_generator (B v))) s :
  wedge (exterior_word [seq P v | v <- s]) (exterior_word [seq Q v | v <- s]) =
    wedge (exterior_word [seq A v | v <- s]) (exterior_word [seq B v | v <- s]).
Proof.
elim: s => [|v s ih] //=.
by rewrite (exterior_word_double_cons (P v) (Q v))
  (exterior_word_double_cons (A v) (B v)) !size_map h ih.
Qed.

(** Source for [product_common_factors]: Federer 1.6.5, p. 26,
    first equality in the final displayed computation. Direct
    block identity for the factors common to xi and eta, with
    a(v)=(v,-v)/2 and b(v)=g(v)=(v,v). *)
Theorem product_common_factors (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) (s : seq V) :
  wedge (exterior_word [seq FedererProduct.P v | v <- s])
    (exterior_word [seq FedererProduct.Q v | v <- s]) =
  wedge (exterior_word [seq FedererProduct.a v | v <- s])
    (exterior_word [seq FedererProduct.g v | v <- s]).
Proof.
apply: paired_exterior_words_replace => v; exact: FedererProduct.product_pair_wedge.
Qed.
