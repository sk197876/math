(** Federer (1969), 3.4.8(10),(13), pp. 332, 336:
    the proved bound on distinct points of each
    actual polynomial fibre bounds the original counting
    multiplicity. Use the sealed counting measure of
    2.1.2, p. 54, with a finite enumeration. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import MappingMultiplicity CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_fibre_multiplicity_bound]: the
    original N(p_m|Z,y)<=k in the proof of
    3.4.8(13), p. 336, from the finite
    fibre and degree conclusions of (10), p. 332. *)
Theorem finite_fibre_multiplicity_bound (R:realType) (X:choiceType) (Y:Type)
    (f:X->Y) (S:set X) k:
  (forall y,finite_set [set x|S x /\f x=y] /\
    forall q:seq X,uniq q ->(forall x,x \in q ->S x /\f x=y) ->(size q<=k)%N) ->
  forall y,(@mapping_multiplicity R X Y f S y<=k%:R%:E)%E.
Proof.
move=>hFibres y.
have [hFinite hSize]:=hFibres y.
have [F hF]:=finite_fsetP.1 hFinite.
have hBound:(size (F:seq X)<=k)%N.
  apply:(hSize (F:seq X) (fset_uniq F))=>x hx.
  have hMember:([set` F]) x:=hx;by rewrite -hF in hMember.
rewrite /mapping_multiplicity /mapping_fibre hF counting_measure_finite lee_fin ler_nat.
exact:hBound.
Qed.
