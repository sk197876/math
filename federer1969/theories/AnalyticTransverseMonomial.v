(** Federer (1969), 3.4.7, p. 325: an
    actual transverse coefficient times a power of xi
    represents the corresponding product in the original
    analytic germ ring. All representatives are local witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing AnalyticGermPowers
  AnalyticPullbackRepresentative AnalyticPullbackSealed WeierstrassTransverseUP WeierstrassTransversePullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_transverse_monomial_representative]: an
    original coefficient pulled back by eta times xi
    to its original natural exponent has the actual
    product germ, supporting P in 3.4.7, p. 325. *)
Theorem analytic_transverse_monomial_representative (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection)
    (fXi:@analytic_representative_type R X NX hNX 0)
    (c:@analytic_representative_type R K NK hNK (projection 0)) i:
  (forall x,analytic_representative_value fXi x = xi x) ->
  exists f:@analytic_representative_type R X NX hNX 0,
    (forall x,analytic_representative_value f x = (xi x)^+i*analytic_representative_value c (projection x)) /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) =
      (@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
        v xi inclusion projection hSplit (analytic_germ c))*
      (analytic_germ fXi:@analytic_germ_ring R X NX hNX 0)^+i.
Proof.
move=>hXi.
have [g [hGValues hGGerm]]:=@analytic_representative_power_exists R X NX hNX 0 fXi i.
pose hProjection:=@weierstrass_transverse_projection_analytic R X K NX NK hNX hNK
  v xi inclusion projection hSplit.
pose pulled:=@analytic_pullback_representative R X K NX NK hNX hNK setT projection 0 hProjection c.
exists (@analytic_multiply_representatives R X NX hNX 0 pulled g);split.
- move=>x.
  change (analytic_representative_value c (projection x)*analytic_representative_value g x =
    (xi x)^+i*analytic_representative_value c (projection x)).
  by rewrite hGValues hXi mulrC.
- rewrite -(@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0)).
  change ((analytic_germ pulled:@analytic_germ_ring R X NX hNX 0)*analytic_germ g =
    (@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
      v xi inclusion projection hSplit (analytic_germ c))*
      (analytic_germ fXi:@analytic_germ_ring R X NX hNX 0)^+i).
  rewrite hGGerm.
  congr (_*_).
  exact:esym (@AnalyticPullback.laws R X K NX NK hNX hNK setT projection 0 hProjection c).
Qed.
