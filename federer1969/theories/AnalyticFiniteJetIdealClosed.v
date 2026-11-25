(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the finite-jet image of every original analytic
    ideal is a closed real vector subspace. The
    actual derivative and scalar arithmetic supply its
    linear laws. No ideal closedness is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis ModuleQuotient
  FiniteSubspaceBasisExistence FiniteNormSubspaceClosed AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives CommutativeIdealUP AnalyticFiniteJetsUP
  AnalyticFiniteJetsSealed AnalyticFiniteJetsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_finite_jet_ideal_image_closed]:
    finite derivative coordinates give a closed image
    of an original ideal, supporting the expanded
    closedness proof for 3.4.8(5), p. 328.
    The source is finite dimensional; the ideal need
    not be proper and the jet prefix may be empty. *)
Theorem analytic_finite_jet_ideal_image_closed (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b) m a
  (I:set (@analytic_germ_ring R X NX hNX a)) (hI:is_commutative_ideal I):
  @closed (real_norm_metric_space (@analytic_finite_jet_norm_laws R X NX hNX m))
    ((@AnalyticFiniteJets.map R X NX hNX m a) @` I).
Proof.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
pose P:=@analytic_finite_jet_space R X NX hNX m.
pose f:=@AnalyticFiniteJets.map R X NX hNX m a.
pose K:set P:=f @` I.
have hZero:K 0.
  exists (0:G);first exact:commutative_ideal_zero hI.
  exact:(@analytic_finite_jet_zero R X NX hNX m a).
have hAdd:forall x y,K x ->K y ->K (x+y).
  move=>x y [alpha ha <-] [beta hb' <-].
  exists (alpha+beta);first exact:(@commutative_ideal_add G I hI alpha beta ha hb').
  exact:(@analytic_finite_jet_add R X NX hNX m a alpha beta).
have hScale:forall c x,K x ->K (c*:x).
  move=>c x [alpha ha <-].
  exists ((analytic_germ (@analytic_constant_representative R X NX hNX a c):G)*alpha).
  - exact:(@commutative_ideal_mul G I hI _ alpha ha).
  - exact:(@analytic_finite_jet_scale R X NX hNX m a c alpha).
pose S:=@Subspace R P K hZero hAdd hScale.
have [q [e he]]:=@analytic_finite_jet_basis_exists R X NX hNX m n b hb.
have [s [d [hd _]]]:=@finite_subspace_basis_exists R P q e he S.
exact:(@finite_norm_subspace_closed R P (@analytic_finite_jet_norm R X NX hNX m)
  (@analytic_finite_jet_norm_laws R X NX hNX m) q e he S s (ex_intro _ d hd)).
Qed.
