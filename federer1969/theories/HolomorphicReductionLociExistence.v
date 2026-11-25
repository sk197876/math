(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the original membership equations determine actual
    reduction sets. The formulas prove existence only;
    downstream arguments use the independent membership laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP SymmetricForms HolomorphicGermFormsSealed RealNormUP HolomorphicGermUP HolomorphicGermRing HolomorphicReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_reduction_loci_exist]: all original
    reduction loci exist with exactly the printed equations,
    including A_0 empty and E_n its printed complement,
    3.4.8(2), p. 326. This asserts no Borel,
    measure, dimension, or stratification conclusion. *)
Theorem holomorphic_reduction_loci_exist (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) n (O:Type)
    (e:'I_n->X) (gamma:'I_n->@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)
    (Q:nat->set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0))
    (rotated:O->set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)):
  exists (A:'I_n.+1->set O) (B C:'I_n->set O) (E:'I_n.+1->set O),
    is_holomorphic_reduction_loci e gamma Q rotated A B C E.
Proof.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
pose A (j:'I_n.+1) (g:O):Prop:=
  (0<j)%N /\exists alpha:G,rotated g alpha /\Q j alpha /\alpha<>0.
pose B (j:'I_n) (g:O):Prop:=
  exists alpha:G,rotated g alpha /\Q (j:nat).+1 alpha /\
    has_nonzero_holomorphic_directional_jet hNX alpha (e j).
pose C (m:'I_n) (g:O):Prop:=forall j:'I_n,(m<=j)%N ->exists delta L:G,
  Q m delta /\~rotated g delta /\Q (m:nat).+1 L /\rotated g (delta*gamma j-L).
pose E (j:'I_n.+1) (g:O):Prop:=~A j g /\
  ((j:nat)=n \/exists m:'I_n,(m:nat)=(j:nat) /\C m g /\
    forall i:'I_n,(m<=i)%N ->B i g).
exists A,B,C,E;constructor.
- by move=>j g.
- by move=>j g.
- by move=>m g.
- move=>m g;split.
  + move=>[hNotA [hLast|[m' [hEq [hC hB]]]]].
    * have hSmall:=ltn_ord m;change ((m:nat)=n) in hLast.
      by rewrite hLast ltnn in hSmall.
    * have hSame:m'=m by apply:val_inj;exact:hEq.
      subst m';by split;last split.
  + move=>[hC [hB hNotA]];split;first exact:hNotA.
    right;exists m;by split;last split.
- move=>g;split;first by move=>[hA _].
  move=>hA;split;first exact:hA.
  by left.
Qed.
