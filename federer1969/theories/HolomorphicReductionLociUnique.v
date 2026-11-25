(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the independent original membership laws determine
    all reduction loci uniquely, including both endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP SymmetricForms HolomorphicGermFormsSealed RealNormUP HolomorphicGermUP HolomorphicGermRing HolomorphicReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_reduction_loci_unique]: the original
    equations uniquely determine A_j, B_j, C_m and E_m,
    3.4.8(2), p. 326. No topological or measure
    conclusion is used to identify the sets. *)
Theorem holomorphic_reduction_loci_unique (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) n (O:Type)
    (e:'I_n->X) (gamma:'I_n->@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)
    (Q:nat->set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0))
    (rotated:O->set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0))
    (A A':'I_n.+1->set O) (B B' C C':'I_n->set O) (E E':'I_n.+1->set O):
  is_holomorphic_reduction_loci e gamma Q rotated A B C E ->
  is_holomorphic_reduction_loci e gamma Q rotated A' B' C' E' ->
  A=A' /\B=B' /\C=C' /\E=E'.
Proof.
move=>hL hL'.
have hA:A=A'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - apply/(@holomorphic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).
    exact:(@holomorphic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).1 hg.
  - apply/(@holomorphic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).
    exact:(@holomorphic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).1 hg.
have hB:B=B'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - apply/(@holomorphic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).
    exact:(@holomorphic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).1 hg.
  - apply/(@holomorphic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).
    exact:(@holomorphic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).1 hg.
have hC:C=C'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - apply/(@holomorphic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).
    exact:(@holomorphic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).1 hg.
  - apply/(@holomorphic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).
    exact:(@holomorphic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).1 hg.
have hE:E=E'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - case:(ltnP (j:nat) n)=>hj.
    + pose m:'I_n:=Ordinal hj.
      have hIndex:j=widen_ord (leqnSn n) m by apply:val_inj.
      rewrite hIndex in hg *.
      apply/(@holomorphic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' m g).
      rewrite -hA -hB -hC.
      exact:(@holomorphic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL m g).1 hg.
    + have hIndex:j=ord_max.
        apply:val_inj;apply/eqP;rewrite eqn_leq hj andbT.
        exact:(ltn_ord j).
      rewrite hIndex in hg *.
      apply/(@holomorphic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' g).
      rewrite -hA.
      exact:(@holomorphic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL g).1 hg.
  - case:(ltnP (j:nat) n)=>hj.
    + pose m:'I_n:=Ordinal hj.
      have hIndex:j=widen_ord (leqnSn n) m by apply:val_inj.
      rewrite hIndex in hg *.
      apply/(@holomorphic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL m g).
      rewrite hA hB hC.
      exact:(@holomorphic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' m g).1 hg.
    + have hIndex:j=ord_max.
        apply:val_inj;apply/eqP;rewrite eqn_leq hj andbT.
        exact:(ltn_ord j).
      rewrite hIndex in hg *.
      apply/(@holomorphic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL g).
      rewrite hA.
      exact:(@holomorphic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' g).1 hg.
by split;last split;last split.
Qed.
