(** Federer (1969), 4.1.5, p. 349: sums and
    scalar multiples of compact uniform test approximations
    have the expected limits and common compact supports.
    These estimates supply the linearity of T independently
    of any choice of convolution representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra ring.
From Federer Require Import Hom RealNormUP CompactUniformApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactUniformApproximationAlgebra.
Variable R:realType.
Variable X:topologicalType.
Variable U:set X.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Local Notation A := (@is_compact_uniform_test_approximation R X U Y NY E value).

(** Source for [compact_uniform_test_approximation_add]:
    the approximation properties used for additivity of
    T in Federer 4.1.5, p. 349. The union of the two
    actual compact support bounds remains inside U. *)
Theorem compact_uniform_test_approximation_add w v P Q:
  A w P ->A v Q ->A (fun x=>w x+v x) (fun e=>P e+Q e).
Proof.
move=>[C [hC [hCU [r [hr [hPOff hPA]]]]]]
  [D [hD [hDU [s [hs [hQOff hQA]]]]]].
exists (C `|` D); split; first exact:compactU hC hD.
split; first by move=>x [hx|hx]; [exact:hCU x hx|exact:hDU x hx].
exists (Num.min r s); split; first by rewrite lt_min hr hs.
split.
- move=>e he hSmall x hx.
  have /andP [her hes]:(e<r)&&(e<s) by rewrite -lt_min.
  have hXC:~C x by move=>h; apply:hx; left.
  have hXD:~D x by move=>h; apply:hx; right.
  have hValue:value (P e+Q e) x=value (P e) x+value (Q e) x:=
    congr1 (fun F:X->Y=>F x) (linearD value (P e) (Q e)).
  by rewrite hValue (hPOff e he her x hXC) (hQOff e he hes x hXD) addr0.
- move=>eta hEta.
  have hHalf:0<eta/2 by rewrite divr_gt0 // ltr0n.
  have[d [hd hP]]:=hPA (eta/2) hHalf.
  have[f [hf hQ]]:=hQA (eta/2) hHalf.
  exists (Num.min d f); split; first by rewrite lt_min hd hf.
  move=>e he hSmall x.
  have /andP [hed hef]:(e<d)&&(e<f) by rewrite -lt_min.
  have hValue:value (P e+Q e) x=value (P e) x+value (Q e) x:=
    congr1 (fun F:X->Y=>F x) (linearD value (P e) (Q e)).
  have hDiff:value (P e) x+value (Q e) x-(w x+v x)=
      (value (P e) x-w x)+(value (Q e) x-v x) by rewrite opprD addrACA.
  rewrite hValue hDiff.
  have hPBound:=hP e he hed x; have hQBound:=hQ e he hef x.
  have hT:=real_seminorm_triangle hNY.1 (value (P e) x-w x) (value (Q e) x-v x).
  lra.
Qed.

(** Source for [compact_uniform_test_approximation_scale]:
    the approximation properties used for homogeneity of
    T in Federer 4.1.5, p. 349. The proof includes
    the zero multiplier and retains the original compact. *)
Theorem compact_uniform_test_approximation_scale w P c:
  A w P ->A (fun x=>c*:w x) (fun e=>c*:P e).
Proof.
move=>[C [hC [hCU [r [hr [hOff hApprox]]]]]].
exists C; split=>//; split=>//; exists r; split=>//; split.
- move=>e he her x hx.
  have hValue:value (c*:P e) x=c*:value (P e) x:=
    congr1 (fun F:X->Y=>F x) (linearZ_LR (hom_as_linear value) c (P e)).
  by rewrite hValue (hOff e he her x hx) scaler0.
- move=>eta hEta.
  have hCPositive:0<`|c|+1 by have:=normr_ge0 c; lra.
  have hSmallError:0<eta/(`|c|+1) by rewrite divr_gt0.
  have[d [hd hBound]]:=hApprox _ hSmallError.
  exists d; split=>// e he hed x.
  have hValue:value (c*:P e) x=c*:value (P e) x:=
    congr1 (fun F:X->Y=>F x) (linearZ_LR (hom_as_linear value) c (P e)).
  rewrite hValue -scalerBr (real_seminorm_scale hNY.1).
  have hB:=hBound e he hed x.
  have hBudget:(`|c|+1)*NY (value (P e) x-w x)<eta.
    by move:hB; rewrite ltr_pdivlMr // mulrC.
  have hLe:`|c|*NY (value (P e) x-w x)<=(`|c|+1)*NY (value (P e) x-w x).
    have hScalar:`|c|<=`|c|+1 by lra.
    have hNZ:0<=NY (value (P e) x-w x):=real_seminorm_nonnegative hNY.1 (value (P e) x-w x).
    exact:(ler_wpM2r hNZ hScalar).
  exact:le_lt_trans hLe hBudget.
Qed.
End CompactUniformApproximationAlgebra.
