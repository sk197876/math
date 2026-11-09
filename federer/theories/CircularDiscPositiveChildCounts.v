(** Federer (1969), 3.3.19, p. 302: the
    initial F_n(D) definition uses EVERY positive integer n.
    Prove its exact count also at n= 1,2,3, independently
    of the stronger separation used at levels n>= 4. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscRefinement
  CircularRegularDirections CircularRegularMinimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Children.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [circular_disc_positive_child_injective]:
    every original positive subdivision has distinct indexed
    centres, 3.3.19, p. 302. The n= 1 case retains its
    full parent-radius disc; n>= 2 uses positive scaling of
    the actual injective cyclic direction map. *)
Theorem circular_disc_positive_child_injective (z:E) (r:R) n:
  0<r ->(0<n)%N ->injective (@circular_disc_child_center R z r n).
Proof.
move=>hr;case:n=>[//|[|n]] hn.
- move=>k l _;by rewrite (ord1 k) (ord1 l).
- pose N:=n.+2.
  change (injective (@circular_disc_child_center R z r N)).
  have hN2:(2<=N)%N by rewrite /N.
  have hNP:(0<N%:R:>R) by rewrite ltr0n /N.
  have hNN:(N%:R:R)!= 0 by rewrite gt_eqF.
  have hN2R:(2<=N%:R:>R) by rewrite ler_nat.
  pose q:R:=N%:R^-1.
  pose c:R:=(1-q)* r.
  have hq:0<q by rewrite /q invr_gt0.
  have hNq:N%:R* q= 1 by rewrite /q mulfV.
  have hFactor:0<1-q by nra.
  have hcP:0<c by rewrite /c;exact:(mulr_gt0 hFactor hr).
  have hcN:c!= 0 by rewrite gt_eqF.
  have hRecover (k:'I_N):c^-1*:(circular_disc_child_center z r k-z)=
      @circular_regular_direction R N k.
    by rewrite /circular_disc_child_center /circular_regular_direction -/q -/c
      addrAC subrr add0r scalerA mulVf // scale1r.
  move=>k l hEqual.
  have hRecovered:=congr1 (fun w:E=>c^-1*:(w-z)) hEqual.
  rewrite !hRecover in hRecovered.
  exact:(@circular_regular_direction_injective R N hN2 k l hRecovered).
Qed.

(** Source for [circular_disc_positive_child_count]:
    the original family F_n(D) has exactly n actual discs
    for EVERY positive n, 3.3.19, p. 302. Positive
    parent radius follows the book's ball convention. *)
Theorem circular_disc_positive_child_count (z:E) (r:R) n:
  0<r ->(0<n)%N ->
  #|` [fset circular_disc_child_center z r k | k:'I_n]|=n.
Proof.
move=>hr hn;rewrite card_imfset;last exact:(@circular_disc_positive_child_injective z r n hr hn).
by rewrite /= -cardE card_ord.
Qed.
End Children.
