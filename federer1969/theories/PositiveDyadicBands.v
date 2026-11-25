(** Federer (1969), 3.2.7, p. 246: supporting
    disjoint positive target bands for the oscillatory
    counterexample. Their endpoints use the already
    proved dyadic scalar laws from 2.10.47, p. 204. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology normedtype lra ring.
From Federer Require Import RealMetricBackground DyadicScaleBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_dyadic_radius]: scaled
    dyadic radius supporting the target level bands
    in Federer 3.2.7, p. 246. *)
Definition positive_dyadic_radius (R:realType) (c:R) (k:nat):R:=c/((2^k)%N)%:R.

(** Source for [positive_dyadic_radius_positive]:
    positivity of every target band radius in
    Federer 3.2.7, p. 246. *)
Lemma positive_dyadic_radius_positive (R:realType) (c:R) (k:nat):
  0<c -> 0<positive_dyadic_radius c k.
Proof. move=>hc; by rewrite /positive_dyadic_radius divr_gt0 // ltr0n expn_gt0. Qed.

(** Source for [positive_dyadic_radius_antitone]:
    nested target scales supporting Federer 3.2.7, p. 246. *)
Lemma positive_dyadic_radius_antitone (R:realType) (c:R) i j:
  0<=c -> (i<=j)%N -> positive_dyadic_radius c j<=positive_dyadic_radius c i.
Proof. move=>hc hij; exact (ler_wpM2l hc (@dyadic_side_antitone R i j hij)). Qed.

(** Source for [positive_dyadic_radius_successor]:
    exact halving supporting the interval-mass calculation
    in Federer 3.2.7, p. 246. *)
Lemma positive_dyadic_radius_successor (R:realType) (c:R) k:
  positive_dyadic_radius c k.+1=positive_dyadic_radius c k/2.
Proof. by rewrite /positive_dyadic_radius dyadic_side_successor mulrA. Qed.

(** Source for [positive_dyadic_band]: open target
    bands between consecutive squared dyadic radii,
    supporting Federer 3.2.7, p. 246. *)
Definition positive_dyadic_band (R:realType) (c:R) k:set (real_line_metric R):=
  `](positive_dyadic_radius c k.+1)^+2,(positive_dyadic_radius c k)^+2[.

(** Source for [positive_dyadic_bands_disjoint]:
    pairwise disjointness of the target intervals used
    for Federer 3.2.7, p. 246. Open endpoints
    avoid an additional overlap convention. *)
Lemma positive_dyadic_bands_disjoint (R:realType) (c:R):
  0<c -> forall i j,i!=j -> forall x,
  positive_dyadic_band c i x -> positive_dyadic_band c j x -> False.
Proof.
move=>hc.
have hSep i j:(i<j)%N -> forall x,
    positive_dyadic_band c i x -> positive_dyadic_band c j x -> False.
  move=>hij x hi hj.
  have hScale:=@positive_dyadic_radius_antitone R c i.+1 j (ltW hc) hij.
  have hPi:=positive_dyadic_radius_positive i.+1 hc.
  have hPj:=positive_dyadic_radius_positive j hc.
  have hSquare:(positive_dyadic_radius c j)^+2<=(positive_dyadic_radius c i.+1)^+2 by nra.
  move:hi hj; rewrite /positive_dyadic_band /= !in_itv /= =>/andP[hiL hiU] /andP[hjL hjU].
  lra.
move=>i j hne x hi hj.
case:(ltngtP i j)=>hOrder; last by rewrite hOrder eqxx in hne.
- exact (hSep i j hOrder x hi hj).
- exact (hSep j i hOrder x hj hi).
Qed.
