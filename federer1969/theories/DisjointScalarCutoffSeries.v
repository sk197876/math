(** Federer (1969), 3.2.20, p. 257: the source
    density is the sum of its disjoint compact-image cutoffs, outside
    the null remainder supplied by 3.2.18, p. 255. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology TotalScalarCutoff NonnegativeSum NonnegativeSumSupport
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_scalar_cutoff]: supporting positivity
    of the auxiliary density cutoffs in Federer 3.2.20,
    p. 257. It follows solely from their on/off laws. *)
Lemma nonnegative_scalar_cutoff (R : realType) (X : Type)
    (A : set X) (J : X -> R) :
  (forall x,(0<=J x)%R) -> forall x,(0<=total_scalar_cutoff A J x)%R.
Proof.
move=> hJ x; case: (pselect (A x))=> hx.
- by rewrite (total_scalar_cutoff_on J hx).
- by rewrite (total_scalar_cutoff_off J hx).
Qed.

(** Source for [disjoint_scalar_cutoff_series]: the source summation
    in Federer 3.2.20, p. 257. Compactness is not needed
    for this algebraic support lemma: disjoint subsets of W and
    a null uncovered remainder suffice. Every cutoff is dominated
    by the total finite density, and the sum identity holds almost
    everywhere without assuming measurability of J. *)
Lemma disjoint_scalar_cutoff_series (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (W : set X) (E : nat -> set X) (J : X -> R) :
  (forall x,(0<=J x)%R) ->
  (forall i,E i `<=` W) ->
  (forall i j,i!=j -> forall x,E i x -> E j x -> False) ->
  mu (W `\` (\bigcup_i E i))=0 ->
  (forall i x,(0<=total_scalar_cutoff (E i) J x<=total_scalar_cutoff W J x)%R) /\
  measure_almost_everywhere mu [set x|
    nonnegative_sum setT (fun i=>(total_scalar_cutoff (E i) J x)%:E)=
      (total_scalar_cutoff W J x)%:E].
Proof.
move=> hJ hSub hDisj hLoss.
have hPi0 i x : (0<=total_scalar_cutoff (E i) J x)%R := @nonnegative_scalar_cutoff R X (E i) J hJ x.
have hP0 x : (0<=total_scalar_cutoff W J x)%R := @nonnegative_scalar_cutoff R X W J hJ x.
split.
- move=> i x; apply/andP; split; first exact: hPi0.
  case: (pselect (E i x))=> hx.
  + by rewrite (total_scalar_cutoff_on J hx) (total_scalar_cutoff_on J (hSub i x hx)).
  + by rewrite (total_scalar_cutoff_off J hx).
- have hOutside : measure_almost_everywhere mu (~` (W `\` (\bigcup_i E i))).
    by rewrite /measure_almost_everywhere setCK.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hOutside)=> x hx.
  change (nonnegative_sum setT (fun i=>(total_scalar_cutoff (E i) J x)%:E)=
    (total_scalar_cutoff W J x)%:E).
  case: (pselect ((\bigcup_i E i) x))=> hIn.
  + have [i hi hEi] := hIn.
    rewrite (total_scalar_cutoff_on J (hSub i x hEi)).
    have hOne : nonnegative_sum setT (fun j=>(total_scalar_cutoff (E j) J x)%:E)=
        (total_scalar_cutoff (E i) J x)%:E.
      have hPos : 0<=(total_scalar_cutoff (E i) J x)%:E by rewrite lee_fin; exact: hPi0.
      have hZero j (_ : setT j) (hji : j!=i) : (total_scalar_cutoff (E j) J x)%:E=0.
        have hEj : ~E j x.
          move=> hEj; exact: (hDisj j i hji x hEj hEi).
        by rewrite (total_scalar_cutoff_off J hEj).
      exact (@nonnegative_sum_single_support R [the choiceType of (nat : Type)] setT
        (fun j=>(total_scalar_cutoff (E j) J x)%:E) i Logic.I hPos hZero).
    by rewrite hOne (total_scalar_cutoff_on J hEi).
  + have hNotW : ~W x by move=> hw; apply: hx; split.
    rewrite (total_scalar_cutoff_off J hNotW).
    apply: nonnegative_sum_zero=> i _.
    have hNotEi : ~E i x by move=> hi; apply: hIn; exists i.
    by rewrite (total_scalar_cutoff_off J hNotEi).
Qed.
