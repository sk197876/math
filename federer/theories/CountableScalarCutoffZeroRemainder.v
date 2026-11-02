(** Federer (1969), 3.2.22, p. 259:
    the disjoint chart densities sum even when the
    omitted source set is null only for the density. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport TotalScalarCutoff
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_scalar_cutoff_zero_remainder]:
    the sum of a_ij in Federer 3.2.22,
    p. 259. Disjoint cutoffs exhaust a nonnegative
    density almost everywhere if the density vanishes
    almost everywhere on the omitted remainder. That
    remainder need not itself be source-null. The
    pointwise support argument allows arbitrary indices;
    the integral application uses a countable family. *)
Lemma countable_scalar_cutoff_zero_remainder (R:realType) (X I:choiceType)
    (rho:set X->\bar R) (hr:is_measure rho) (A:set X) (D:set I)
    (P:I->set X) (J:X->R):
  (forall x,(0<=J x)%R) ->(forall i,D i ->P i `<=` A) ->
  (forall i j,D i ->D j ->i<>j ->P i `&` P j=set0) ->
  measure_almost_everywhere_on rho (A `\` (\bigcup_(i in D) P i)) [set x|J x=0%R] ->
  measure_almost_everywhere rho [set x|
    nonnegative_sum D (fun i=>(total_scalar_cutoff (P i) J x)%:E)=(total_scalar_cutoff A J x)%:E].
Proof.
move=>hPositive hSub hDisjoint hZero.
apply:(measure_almost_everywhere_mono hr _
  ((measure_almost_everywhere_on_implication _ _ _).1 hZero))=>x hZeroX.
change (nonnegative_sum D (fun i=>(total_scalar_cutoff (P i) J x)%:E)=(total_scalar_cutoff A J x)%:E).
have [hIn|hIn]:=pselect ((\bigcup_(i in D) P i) x).
- have [i hi hPi]:=hIn.
  have hPos:0<=(total_scalar_cutoff (P i) J x)%:E.
    rewrite (total_scalar_cutoff_on J hPi) lee_fin; exact:(hPositive x).
  have hOther j (hj:D j) (hji:j!=i):(total_scalar_cutoff (P j) J x)%:E=0.
    have hNotP:~P j x.
      move=>hPj; have hNe:j<>i by move=>hEq; by rewrite hEq eqxx in hji.
      have hEmpty:=hDisjoint j i hj hi hNe; have hMember:(P j `&` P i) x:=conj hPj hPi.
      by rewrite hEmpty in hMember.
    by rewrite (total_scalar_cutoff_off J hNotP).
  rewrite (@nonnegative_sum_single_support R I D (fun i=>(total_scalar_cutoff (P i) J x)%:E)
    i hi hPos hOther).
  by rewrite (total_scalar_cutoff_on J hPi) (total_scalar_cutoff_on J (hSub i hi x hPi)).
- have hSum:nonnegative_sum D (fun i=>(total_scalar_cutoff (P i) J x)%:E)=0.
    apply:nonnegative_sum_zero=>i hi.
    have hNotPi:~P i x by move=>hp; apply:hIn; by exists i.
    by rewrite (total_scalar_cutoff_off J hNotPi).
  rewrite hSum.
  have [hx|hx]:=pselect (A x).
  + by rewrite (total_scalar_cutoff_on J hx) (hZeroX (conj hx hIn)).
  + by rewrite (total_scalar_cutoff_off J hx).
Qed.
