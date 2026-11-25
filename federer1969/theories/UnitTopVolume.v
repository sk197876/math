(** Federer (1969), 1.7.8, p. 34: a prescribed unit top vector determines
    the orientation. This supporting lemma compares it with the top product
    of any orthonormal basis, using 1.3.4 and 1.7.5. In dimension zero both
    scalar volumes 1 and -1 are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorNorm
  LinearBasis OrthonormalFamilies FiniteExteriorPowers TopExteriorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_top_volume_scalar]: Federer 1.7.8,
    p. 34, supporting comparison: a unit top vector is c times
    an orthonormal top product, with c squared equal to one.
    This covers dimension zero without assuming a basis of volume -1. *)
Theorem unit_top_volume_scalar (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1) :
  exists c : R, E = c *: e_lambda e (ord_tuple n) /\ c^+2 = 1.
Proof.
have hu : exterior_norm h2 hB (e_lambda e (ord_tuple n)) = 1 :=
  orthonormal_product_unit_norm h2 hB ho.
have hn : e_lambda e (ord_tuple n) != 0.
  apply/eqP=> hz; move: hu; rewrite hz exterior_norm_zero => /eqP.
  by rewrite eq_sym oner_eq0.
have [c hc] := @nonzero_top_vector_spans R h2 V n e he
  (e_lambda e (ord_tuple n)) hn E.
exists c; split=> //.
have habs : `|c| = 1 by move: hE; rewrite hc exterior_norm_scale hu mulr1.
by apply/eqP; rewrite sqr_norm_eq1 habs eqxx.
Qed.
