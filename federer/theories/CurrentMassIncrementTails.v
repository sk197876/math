(** Federer (1969), 4.1.12, pp. 368–369: finite
    partial sums of the two original current series
    have uniformly small mass tails. This supporting
    telescoping estimate uses the original mass
    linear-combination bound, retaining all zero masses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassSealed CurrentMassFiniteAlgebra
  CurrentFiniteMassLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentMassIncrementTails.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:(R_n R n)->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [current_mass_increment_tail_bound]:
    if consecutive current increments have mass at
    most t_k-t_(k+1), every later displacement from
    index N has mass at most t_N. This is
    the finite telescoping estimate for the original
    series in Federer 4.1.12, pp. 368–369. *)
Theorem current_mass_increment_tail_bound (u:nat->C) (t:nat->R):
  (forall k,0<=t k)->
  (forall k,(M ((u k.+1-u k)%R)<=(t k-t k.+1)%:E)%E)->
  forall N K,(N<=K)%N->(M ((u K-u N)%R)<=(t N)%:E)%E.
Proof.
move=>hT hIncrement N K hNK.
have hTail k:(M ((u (N+k)%N-u N)%R)<=(t N-t (N+k)%N)%:E)%E.
  elim:k=>[|k hPrevious].
  - by rewrite addn0 subrr current_mass_zero subrr.
  - rewrite addnS.
    have hSum: u (N+k)%N.+1-u N=
      (u (N+k)%N.+1-u (N+k)%N)+(u (N+k)%N-u N) by rewrite addrA subrK.
    rewrite hSum.
    have h:=@current_finite_mass_linear_bound R h2 n m U hU 1
      (u (N+k)%N.+1-u (N+k)%N) (u (N+k)%N-u N)
      (t (N+k)%N-t (N+k)%N.+1) (t N-t (N+k)%N)
      (hIncrement (N+k)%N) hPrevious.
    rewrite scale1r normr1 mul1r in h.
    have hCoefficient:(t (N+k)%N-t (N+k)%N.+1)+(t N-t (N+k)%N)=t N-t (N+k)%N.+1 by ring.
    by rewrite hCoefficient in h.
have h:=hTail (K-N)%N;rewrite subnKC in h;last exact:hNK.
apply:(le_trans h);rewrite lee_fin lerBlDr.
rewrite -[leLHS]addr0 lerD2l;exact:(hT K).
Qed.
End CurrentMassIncrementTails.
