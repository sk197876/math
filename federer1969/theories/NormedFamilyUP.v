(** Federer (1969), 3.1.1(4), p. 210: the finite Cartesian product
    of possibly different normed vector spaces. The product is specified
    by its linear coordinates, their bijection with tuples, and the sum
    norm. This auxiliary choice of an equivalent finite-product norm
    is explicit; it is not an additional hypothesis on the factors. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_normed_family]: abstract product laws supporting
    Federer 3.1.1(4), p. 210. Every tuple has a unique product element,
    the coordinates are linear, and its norm is the sum of the factor
    norms. Neither finite dimension nor completeness is required. *)
Record is_normed_family (R : realType) m (V : 'I_m -> lmodType R)
    (N : forall i, V i -> R) (P : lmodType R)
    (coordinate : forall i, Hom P (V i)) (PN : P -> R) : Prop := {
  (** Source for [normed_family_extensional]: equality of product
      elements is equality of every coordinate, supporting 3.1.1(4), p. 210. *)
  normed_family_extensional : forall x y,
    (forall i, coordinate i x=coordinate i y) -> x=y;
  (** Source for [normed_family_surjective]: every tuple is represented
      in the product used in 3.1.1(4), p. 210. *)
  normed_family_surjective : forall x : {dffun forall i, V i},
    exists u : P, forall i, coordinate i u=x i;
  (** Source for [normed_family_norm]: the chosen sum norm on the
      product supporting 3.1.1(4), p. 210. *)
  normed_family_norm : forall u, PN u=\sum_(i<m) N i (coordinate i u)
}.
