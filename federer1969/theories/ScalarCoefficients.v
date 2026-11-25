(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import AlternatingAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3: take W=R. The scalar algebra uses the same field
    multiplication and unit as in the preceding alternating algebra. *)
(** Source for [scalar_bilinear]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma scalar_bilinear (K : fieldType) :
  @bilinear K (GRing.Lmodule.clone K K^o _) (GRing.Lmodule.clone K K^o _)
    (GRing.Lmodule.clone K K^o _) (fun x y : K^o => x*y).
Proof.
split.
- move=> y a x z; change ((a*x+z)*y = a*(x*y)+z*y); by rewrite mulrDl mulrA.
- move=> x a y z; change (x*(a*y+z) = a*(x*y)+x*z); by rewrite mulrDr mulrCA.
Qed.
(** Source for [scalar_algebra]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition scalar_algebra (K : fieldType) : algebra K :=
  @Algebra K (GRing.Lmodule.clone K K^o _) (fun x y => x*y) 1
    (scalar_bilinear K) (@mulrA K) (@mul1r K) (@mulr1 K).

(** Source for [scalar_delta_product]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma scalar_delta_product (K : fieldType) (I T : eqType) (f g : I -> T) xs :
  foldr (fun x y : K => x*y) 1 [seq if f i == g i then 1 else 0 | i <- xs] =
    if all (fun i => f i == g i) xs then 1 else 0.
Proof.
elim: xs => [|i xs ih] //=; rewrite ih.
by case: (f i == g i); case: (all _ xs); rewrite ?mul1r ?mul0r.
Qed.
