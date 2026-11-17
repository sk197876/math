(** Federer (1969), 3.4.7, p. 325: specialize the
    transverse coefficient germs at their original centre.
    Monic degree survives even when that coefficient map
    is not injective. This supports the distinguished factors. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import PolynomialCoefficientMapUP CommutativePolynomialDegreeUP
  CommutativePolynomialMonicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_coefficient_map_monic_degree]:
    specialization preserves the degree of every original
    monic factor in 3.4.7, p. 325. No faithful
    specialization hypothesis is required. *)
Theorem polynomial_coefficient_map_monic_degree (A C:comNzRingType)
    (B D:Type) (source:B->nat->A) (target:D->nat->C)
    (phi:{rmorphism A->C}) (M:B->D) (P:B) n:
  is_polynomial_coefficient_map source target phi M ->
  is_monic_polynomial source P n ->is_monic_polynomial target (M P) n.
Proof.
move=>hMap [[hNonzero hHigher] hLeading].
have hTarget:target (M P) n = 1 by rewrite hMap hLeading rmorph1.
split;last exact:hTarget.
split.
- rewrite hTarget;move=>hZero.
  have hOne:(1:C)!=0:=oner_neq0 C.
  by rewrite hZero eqxx in hOne.
- move=>i hi;by rewrite hMap hHigher // rmorph0.
Qed.
