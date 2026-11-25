(** Federer (1969), 3.3.20, pp. 306–308: the exact number of actual Phi children. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals.
From Federer Require Import CompactIntervalGauge EqualCostIntervalFamilyUP EqualCostIntervalEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [equal_cost_original_interval_family_count]: actual
    Phi(J,n) has exactly n members, as used in the original square
    refinements in 3.3.20, pp. 306–308. The existing independently
    proved injective ordinal enumeration supplies the cardinality. *)
Lemma equal_cost_original_interval_family_count (R:realType) (h:R->R)
    (J:compact_real_intervals R) n F:
  is_equal_cost_interval_family h J n F ->#|` F|=n.
Proof.
move=>hF.
have [_ [a [b [s [t [f [_ [_ [_ [_ [_ [hInject hImage]]]]]]]]]]]]:=
  equal_cost_interval_ordinal_enumeration hF.
rewrite hImage card_imfset;last exact:hInject.
have hEqual:enum_finmem (mem_fin (fin_finpred (enum 'I_n)))=i enum 'I_n.
  move=>i;by rewrite enum_finmemE /=.
have hPerm:=uniq_perm (enum_finmem_uniq _) (enum_uniq _) hEqual.
by rewrite (perm_size hPerm) size_enum_ord.
Qed.
