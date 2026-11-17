(** Federer (1969), 3.4.8(1), p. 326:
    actual coordinate germs exist uniquely. The
    original finite source basis makes every coordinate
    functional bounded. Analytic representatives serve
    only as local existence witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis NormFiniteLinearBound
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticGermRingLaws
  PointedFunctionalGermExistence AnalyticCoordinateGermsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_coordinate_germs_exist]: each
    original omega_j has an actual analytic germ,
    3.4.8(1), p. 326. Every chosen representative
    remains hidden from the downstream interface. *)
Theorem analytic_coordinate_germs_exist (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o):
  exists gamma:'I_n->@analytic_germ_ring R X NX hNX 0,is_analytic_coordinate_germs omega gamma.
Proof.
have hEach j:exists f:@analytic_representative_type R X NX hNX 0,
    forall x,analytic_representative_value f x = omega j x.
  have hBound:=@norm_finite_linear_bounded R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) n e he (omega j).
  have [f hF]:=@pointed_functional_representative_exists R X NX hNX 0 (omega j) hBound.
  exists f=>x;by rewrite hF subr0.
have [f hF]:=choice hEach.
exists (fun j=>analytic_germ (f j))=>j g hG.
apply:analytic_germ_pointwise_equality=>x;by rewrite hG hF.
Qed.

(** Source for [analytic_coordinate_germs_unique]: the
    original representative equations uniquely determine
    every coordinate germ, 3.4.8(1), p. 326. *)
Lemma analytic_coordinate_germs_unique (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) (gamma delta:'I_n->@analytic_germ_ring R X NX hNX 0):
  is_analytic_coordinate_germs omega gamma ->is_analytic_coordinate_germs omega delta ->gamma = delta.
Proof.
move=>hGamma hDelta;apply:funext=>j.
have hBound:=@norm_finite_linear_bounded R X R^o NX (fun z:R^o=>`|z|) hNX
  (@scalar_absolute_value_norm R) n e he (omega j).
have [f hF]:=@pointed_functional_representative_exists R X NX hNX 0 (omega j) hBound.
have hValues x:analytic_representative_value f x = omega j x by rewrite hF subr0.
by rewrite -(hGamma j f hValues) -(hDelta j f hValues).
Qed.
