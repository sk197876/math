(** Federer (1969), 3.4.8(2), p. 326:
    the independent original membership laws determine
    all reduction loci uniquely, including both endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermRing AnalyticReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_loci_unique]: the original
    equations uniquely determine A_j, B_j, C_m and E_m,
    3.4.8(2), p. 326. No topological or measure
    conclusion is used to identify the sets. *)
Theorem analytic_reduction_loci_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (O:Type)
    (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
    (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
    (rotated:O->set (@analytic_germ_ring R X NX hNX 0))
    (A A':'I_n.+1->set O) (B B' C C':'I_n->set O) (E E':'I_n.+1->set O):
  is_analytic_reduction_loci e gamma Q rotated A B C E ->
  is_analytic_reduction_loci e gamma Q rotated A' B' C' E' ->
  A=A' /\B=B' /\C=C' /\E=E'.
Proof.
move=>hL hL'.
have hA:A=A'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - apply/(@analytic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).
    exact:(@analytic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).1 hg.
  - apply/(@analytic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).
    exact:(@analytic_reduction_A_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).1 hg.
have hB:B=B'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - apply/(@analytic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).
    exact:(@analytic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).1 hg.
  - apply/(@analytic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).
    exact:(@analytic_reduction_B_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).1 hg.
have hC:C=C'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - apply/(@analytic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).
    exact:(@analytic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).1 hg.
  - apply/(@analytic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL j g).
    exact:(@analytic_reduction_C_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' j g).1 hg.
have hE:E=E'.
  apply:funext=>j;apply/seteqP;split=>g hg.
  - case:(ltnP (j:nat) n)=>hj.
    + pose m:'I_n:=Ordinal hj.
      have hIndex:j=widen_ord (leqnSn n) m by apply:val_inj.
      rewrite hIndex in hg *.
      apply/(@analytic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' m g).
      rewrite -hA -hB -hC.
      exact:(@analytic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL m g).1 hg.
    + have hIndex:j=ord_max.
        apply:val_inj;apply/eqP;rewrite eqn_leq hj andbT.
        exact:(ltn_ord j).
      rewrite hIndex in hg *.
      apply/(@analytic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' g).
      rewrite -hA.
      exact:(@analytic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL g).1 hg.
  - case:(ltnP (j:nat) n)=>hj.
    + pose m:'I_n:=Ordinal hj.
      have hIndex:j=widen_ord (leqnSn n) m by apply:val_inj.
      rewrite hIndex in hg *.
      apply/(@analytic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL m g).
      rewrite hA hB hC.
      exact:(@analytic_reduction_E_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' m g).1 hg.
    + have hIndex:j=ord_max.
        apply:val_inj;apply/eqP;rewrite eqn_leq hj andbT.
        exact:(ltn_ord j).
      rewrite hIndex in hg *.
      apply/(@analytic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL g).
      rewrite hA.
      exact:(@analytic_reduction_E_last_membership _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL' g).1 hg.
by split;last split;last split.
Qed.
