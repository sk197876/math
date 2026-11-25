(** Federer (1969), 4.1.24, p. 382: actual
    current prefixes with nonnegative vanishing telescoping
    mass tails are mass Cauchy. Reuse the preceding
    exact increment-tail estimate and finite mass bounds.
    No normality or representation of the prefixes is
    required. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentMassConvergenceUP
  CurrentMassIncrementTails CurrentFiniteMassLinearBound CurrentFiniteMassNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_mass_cauchy_from_tails]: the
    original current series is Cauchy for mass when
    all its exact tails tend to zero, 4.1.24,
    p. 382. The bound is on every ordered
    pair of sufficiently late indices. *)
Theorem current_mass_cauchy_from_tails (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (u:nat->@current_space R h2 n U hU m) (t:nat->R):
  (forall k,0<=t k)->
  (forall k,(@CurrentMass.value R h2 n m U hU (u k.+1-u k)<=(t k-t k.+1)%:E)%E)->
  (forall epsilon:R,0<epsilon->exists k,t k<epsilon)->
  @is_current_mass_cauchy_sequence R h2 n m U hU u.
Proof.
move=>hT hIncrement hSmall epsilon hEpsilon.
have hThird:0<epsilon/3 by rewrite divr_gt0 //;lra.
have[N hN]:=hSmall (epsilon/3) hThird.
exists N=>i j hNi hNj.
have hFirst:=@current_mass_increment_tail_bound R h2 n m U hU u t hT hIncrement N i hNi.
have hSecond:=@current_mass_increment_tail_bound R h2 n m U hU u t hT hIncrement N j hNj.
have hSecondFinite:(@CurrentMass.value R h2 n m U hU (u j-u N)< +oo)%E.
  exact:le_lt_trans hSecond (ltry (t N)).
have hNeg:=@current_finite_mass_negation R h2 n m U hU (u j-u N) hSecondFinite.
have hReverse:u N-u j= -(u j-u N) by rewrite opprB.
have hBack:(@CurrentMass.value R h2 n m U hU (u N-u j)<=(t N)%:E)%E.
  by rewrite hReverse hNeg.
have hBound:=@current_finite_mass_linear_bound R h2 n m U hU 1
  (u i-u N) (u N-u j) (t N) (t N) hFirst hBack.
rewrite scale1r normr1 mul1r addrA subrK in hBound.
apply:(le_lt_trans hBound);rewrite lte_fin;lra.
Qed.
