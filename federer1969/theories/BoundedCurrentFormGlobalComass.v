(** Federer (1969), 4.1.19, p. 377: the
    selected bounded representatives have finite literal global
    comass on a nonempty U. This uses the
    unchanged pointwise supremum of 4.1.7, p. 358;
    no essential supremum replaces that original definition. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import AlternatingForms RealNormUP GrassmannAbbreviations
  CurrentCoefficientNorms CurrentGlobalComassSealed CurrentGlobalComassBound
  CurrentGlobalComassWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_bounded_form_global_comass_value]:
    finite actual global comass of a selected
    bounded form in Federer 4.1.19, p. 377.
    Nonempty U is explicit because the original
    supremum is minus infinity on an empty
    domain. This supporting implication changes no
    current or cochain hypothesis. *)
Theorem current_bounded_form_global_comass_value
    (R : realType) (h2 : (1+1:R)!=0) n d
    (U : set (R_n R n))
    (phi : R_n R n -> A_m (R_n R n) R^o d) (c : R) :
  (exists x, U x) ->
  (forall x, U x -> @current_form_comass R h2 n d (phi x)<=c) ->
  exists a : R, 0<=a /\
    @CurrentGlobalComass.value R h2 n d U phi=a%:E /\ a<=c.
Proof.
move=> [x hx] hCap.
pose M := @CurrentGlobalComass.value R h2 n d U phi.
have hUpper : (M<=c%:E)%E :=
  (@current_global_comass_bound R h2 n d U phi c).2 hCap.
have hPoint := @current_global_comass_point_lower R h2 n d U phi x hx.
have hNonnegative : (0<=M)%E.
  apply: (le_trans _ hPoint).
  rewrite lee_fin.
  exact: (real_seminorm_nonnegative (@current_form_comass_real_norm R h2 n d).1).
have hFinite : M \is a fin_num.
  rewrite (ge0_fin_numE hNonnegative).
  exact: (le_lt_trans hUpper (ltry c)).
pose a := fine M.
have hValue : M=a%:E by rewrite /a fineK.
exists a; split.
- by rewrite -lee_fin -hValue.
split; first exact: hValue.
by rewrite hValue lee_fin in hUpper.
Qed.
