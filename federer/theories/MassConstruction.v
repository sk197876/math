(** Federer (1969), 1.8.1, p. 38: existence of the mass supremum in finite
    dimension. This private witness uses real order completeness and is
    exposed only through sealing. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP ExteriorNorm ExteriorGrading
  AlternatingCoordinates AlternatingPairing LinearBasis
  ComassUP MassUP MassBounds MassEuclidean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [mass_exists]: Federer 1.8.1, p. 38,
    supporting existence of the defining dual supremum: the comass
    unit ball contains zero and its evaluations have a finite upper bound. *)
Theorem mass_exists (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N)
    (kappa : A_m V R^o m -> R) (hk : forall phi, is_comass h2 hB phi (kappa phi))
    (x : exterior_power V m) : exists d, is_mass kappa x d.
Proof.
pose D := (fun phi => pairing x phi) @` [set phi | kappa phi <= 1].
have hn : D !=set0.
  exists (pairing x 0); exists 0 => //.
  change (kappa (0 : A_m V R^o m) <= 1).
  by rewrite (@comass_function_zero R h2 V B hB m hm kappa hk).
have hb : ubound D (Num.sqrt (('C(n,m))%:R : R) * exterior_norm h2 hB x).
  move=> r [phi hphi <-].
  exact (@mass_unit_evaluation_bound R h2 V B hB n e he m hm kappa hk x phi hphi).
have hu : has_ubound D by exists (Num.sqrt (('C(n,m))%:R : R) * exterior_norm h2 hB x).
have hd : has_sup D by split.
exists (sup D); constructor.
- move=> phi hphi; apply: (sup_upper_bound hd); by exists phi.
- move=> eps heps; have [r [phi hphi hpr] hr] := sup_adherent heps hd.
  exists phi; split=> //; by rewrite hpr.
Qed.
