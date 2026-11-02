(** Federer (1969), 2.4.12, p. 88, final parenthesis: every
    finite-dimensional normed space is reflexive. The algebraic statement
    below is a supporting step; identification of the continuous dual with
    the algebraic dual in finite dimension is separate. Neither example
    itself states the finite-dimensional surjectivity proved below. The
    algebraic result holds over any field, a strengthening of the
    real-scalar background needed in Federer 2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom LinearBasis FiniteDualDimension Biorthogonal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_algebraic_bidual_representative]: supporting
    algebraic representation for finite-dimensional reflexivity in Federer
    2.4.12, p. 88. Every algebraic functional on the dual
    is evaluation at a vector. A finite basis is the only dimension premise. *)
Theorem finite_algebraic_bidual_representative (K : fieldType) (I : finType)
    (V : lmodType K) (e : I -> V) (he : is_basis e)
    (ell : Hom (Hom V K^o) K^o) :
  exists y : V, forall a : Hom V K^o, ell a = a y.
Proof.
pose y := \sum_i ell (dual_basis he i) *: e i.
exists y.
apply: (basis_induction (dual_basisP he))=> [|a b ha hb|c a ha|i].
- by rewrite linear0 hom_zeroE.
- rewrite linearD hom_addE.
  change (ell a + ell b = a y + b y).
  by rewrite ha hb.
- rewrite linearZ hom_scaleE.
  change (c *: ell a = c *: a y).
  by rewrite ha.
change (ell (dual_basis he i)=dual_basis he i y).
symmetry; apply: (@biorthogonal_sum K V I (dual_basis he) e _ (fun j => ell (dual_basis he j)) i).
by move=> j k; rewrite dual_basisE eq_sym.
Qed.
