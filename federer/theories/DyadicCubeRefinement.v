(** Federer (1969), 2.10.47, p. 204: each new cube belongs to a preceding
    cube. These consequences are derived from the abstract coordinate law
    rather than an implementation of the grid. Source context:
    DyadicCubeGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric DyadicCubeGridUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Grid.
Variable R : realType.
Variable n : nat.
Variable a : R_n R n.
Variable Q : forall j, dyadic_cube_indices n j ->
  set (inner_metric_space (@euclidean_inner_productP R n)).
Arguments Q j _ _ : clear implicits.
Hypothesis hQ : is_dyadic_cube_grid a Q.

(** Source for [dyadic_cube_successor_parent]: every cube
    of H_(j+1) is contained in one of H_j, as
    required by the subdivision in 2.10.47, p. 204. *)
Lemma dyadic_cube_successor_parent j s : exists t, Q j.+1 s `<=` Q j t.
Proof.
have hidx i : ((s i)%/2<(2^j))%N.
  rewrite ltn_divLR // -expnSr; exact: ltn_ord.
pose t : dyadic_cube_indices n j := [ffun i=>Ordinal (hidx i)].
exists t=> x hx; apply/(@hQ j t)=> i.
have /andP [hlo hhi] := (proj1 (@hQ j.+1 s x) hx) i.
have hd : (0 : R)<=((2^j.+1)%N)%:R^-1 by rewrite invr_ge0 ler0n.
have hscale : (((2^j.+1)%N)%:R : R)=((2^j)%N)%:R*2 by rewrite expnSr natrM.
have hcancel k : (((k*2)%N)%:R : R)/((2^j.+1)%N)%:R=k%:R/((2^j)%N)%:R.
  by rewrite hscale natrM invfM mulrACA divff ?mulr1 ?pnatr_eq0.
have hl : (((s i)%/2)%:R : R)/((2^j)%N)%:R<=(s i)%:R/((2^j.+1)%N)%:R.
  rewrite -(hcancel ((s i)%/2)%N); apply: ler_wpM2r; first exact hd.
  by rewrite ler_nat leq_divM.
have hu : (((s i).+1)%:R : R)/((2^j.+1)%N)%:R<=(((s i)%/2).+1)%:R/((2^j)%N)%:R.
  rewrite -(hcancel ((s i)%/2).+1); apply: ler_wpM2r; first exact hd.
  by rewrite ler_nat -ltn_divLR // ltnSn.
rewrite /t ffunE /=; apply/andP; split; lra.
Qed.

(** Source for [dyadic_cube_coarse_parent]: every eligible
    finer cube lies in one H_k cell for k<=j,
    used in 2.10.47(1), pp. 204–205. *)
Lemma dyadic_cube_coarse_parent k j : (k<=j)%N ->
  forall s, exists t, Q j s `<=` Q k t.
Proof.
elim: j=> [|j IH] hkj s.
- have -> : k=0%N by move: hkj; rewrite leqn0=> /eqP.
  by exists s.
- case: (eqVneq k j.+1)=> [->|hne]; first by exists s.
  have hprev : (k<=j)%N by move: hkj; rewrite leq_eqVlt (negPf hne) /= ltnS.
  have [t ht] := dyadic_cube_successor_parent s.
  have [u hu] := IH hprev t.
  exists u=> x hx; exact: hu _ (ht x hx).
Qed.
End Grid.
