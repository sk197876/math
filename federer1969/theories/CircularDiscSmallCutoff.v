(** Federer (1969), 3.3.19, p. 302: the
    original positive radius cutoff simultaneously enforces
    all three printed scalar inequalities. Exact positive
    original radii convert a large-index result into the
    original condition rho_n<=delta. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularTrigonometrySealed CircularCoefficientMargins.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Cutoff.
Variable R:realType.
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [factorial_disc_radius_antitone]: all-index
    order of the actual radii, supporting the original
    radius cutoff in 3.3.19, p. 302. The
    already proved strict single-step decrease suffices. *)
Lemma factorial_disc_radius_antitone i j:(i<=j)%N ->rho j<=rho i.
Proof.
move=>hij.
have hEq:(i+(j-i)=j)%N by rewrite subnKC.
rewrite -hEq;elim:(j-i)%N=>[|k ih];first by rewrite addn0.
have hIndex:(i+k.+1=(i+k).+1)%N by rewrite addnS.
rewrite hIndex;exact:le_trans (ltW (@factorial_disc_radius_decreases R N rho hs (i+k)%N)) ih.
Qed.

(** Source for [circular_disc_small_radius_cutoff]: exact
    original quantified choice of delta in 3.3.19,
    p. 302. With original level n=j+4, rho_n<=delta
    implies n>=5 and both printed sine inequalities.
    No supplied asymptotic constant or cutoff is required. *)
Theorem circular_disc_small_radius_cutoff (lam:R):0<lam ->lam<p ->
  exists d:R,0<d /\forall j:nat,rho j.+1<=d ->
    (5<=j+4)%N /\lam<((j+4)%:R-1)* S (p/(j+4)%:R) /\
    lam*(1/2+((j+4).+1)%:R^-1)<((j+4)%:R-1)* S (p/(j+4)%:R)-1.
Proof.
move=>hlam hlamP.
have [K hK]:=@circular_coefficient_large_subdivision R lam hlam hlamP.
have hPositive:=@factorial_disc_radius_positive R N rho hs K.
exists (rho K/2);split;first by rewrite divr_gt0 // ltr0n.
move=>j hRadius.
have hLarge:(K<j.+1)%N.
  case:(ltnP K j.+1)=>[h|hSmall];first by [].
  have hOrder:=@factorial_disc_radius_antitone j.+1 K hSmall.
  exfalso;lra.
have hKj:(K<=j)%N by move:hLarge;rewrite ltnS.
have hKn:(K<=j+4)%N:=leq_trans hKj (leq_addr 4 j).
exact:hK (j+4)%N hKn.
Qed.
End Cutoff.
