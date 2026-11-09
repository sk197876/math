(** Federer (1969), 3.3.18, p. 301: actual finite
    geometric weights give arbitrarily large degree-one density spikes. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import GeometricErrorBudget GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [atomic_radial_cluster_budget_small]: supporting
    the countably supported false-converse example in Federer
    3.3.18, p. 301. Every sufficiently late ORIGINAL positive
    budget is smaller than any prescribed positive bound, by
    its actual geometric tail formula and proved contraction. *)
Lemma atomic_radial_cluster_budget_small (R:realType) (e:R):
  0<e ->exists K:nat,forall k,(K<=k)%N ->geometric_error_budget (1:R) k<e.
Proof.
move=>he.
have hHalf:(0<(2:R)^-1<1) by apply/andP; split; rewrite ?invr_gt0 ?invf_lt1 // ?ltr0n ?ltr1n.
have hM:(0<=(1/2:R)) by lra.
have [K hK]:=@geometric_uniform_tail R (2^-1)%R (1/2)%R e hHalf hM he.
exists K=>k hk.
have hTail:(geometric_error_tail (1:R) k<e).
  rewrite /geometric_error_tail mulrC; exact:hK k hk.
have hNext:=@geometric_error_tail_nonnegative R 1%R k.+1 (@ler01 R).
rewrite /geometric_error_budget; lra.
Qed.

(** Source for [atomic_radial_cluster_spike_scalar]: supporting
    large normalized mass in the converse counterexample of
    Federer 3.3.18, p. 301. Mass c*w at actual radius w squared
    gives normalized density c*w/(2*w squared); it exceeds any
    prescribed real b once the ORIGINAL weight w is small enough. *)
Lemma atomic_radial_cluster_spike_scalar (R:realType) (b c w:R):
  0<c ->0<w ->w<=c/(2*(`|b|+1)) ->b<=c*w/(2*w^+2).
Proof.
move=>hc hw hSmall.
have hB:(0<`|b|+1) by have:=normr_ge0 b; lra.
have hDen:(0<2*(`|b|+1)) by rewrite mulr_gt0 // ltr0n.
have hProduct:(w*(2*(`|b|+1))<=c) by move:hSmall; rewrite ler_pdivlMr.
have hScaled:=ler_wpM2r (ltW hw) hProduct.
have hMassDen:(0<2*w^+2) by rewrite mulr_gt0 ?exprn_gt0 // ltr0n.
rewrite ler_pdivlMr //.
have hBound:=ler_norm b.
have hW2:(0<=w^+2) by rewrite sqr_ge0.
have hOrder:=ler_wpM2r hW2 hBound.
nra.
Qed.
