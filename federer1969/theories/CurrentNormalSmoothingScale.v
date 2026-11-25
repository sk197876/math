(** Federer (1969), 4.1.18, p. 376: choose
    a positive smoothing radius below the original
    support allowance with epsilon N(R_i) below its
    independent flat-error budget. Reuse finite normal
    mass from 4.1.7, p. 358, and
    the earlier positive-product cutoff of 3.2.36,
    p. 272. Zero normal mass is retained. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces NormalCurrentsUP CurrentNormalMass NormalCurrentFiniteMass
  PositiveUniformErrorRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_normal_smoothing_scale]: the
    two simultaneous printed radius requirements in
    Federer 4.1.18, p. 376. Finite normal
    mass is derived from the chosen normal current,
    rather than imposed on the original flat input. *)
Theorem current_normal_smoothing_scale (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m) (r eta:R):
  @is_normal_current R h2 n U hU m T->0<r->0<eta->
  exists epsilon:R,0<epsilon /\epsilon<=r /\
    (epsilon%:E* @current_normal_mass R h2 n U hU m T<eta%:E)%E.
Proof.
move=>hNormal hr hEta.
pose N:=@current_normal_mass R h2 n U hU m T.
have hNonnegative:(0<=N)%E:=@current_normal_mass_nonnegative R h2 n U hU m T.
have hFinite:(N< +oo)%E:=@normal_current_finite_normal_mass R h2 n U hU m T hNormal.
have hNumber:N \is a fin_num by rewrite (ge0_fin_numE hNonnegative).
pose c:=fine N.
have hN:N=c%:E by rewrite /c fineK.
have hc:0<=c by have h:=hNonnegative;rewrite hN lee_fin in h.
have[d [hd [hOne hCost]]]:=@positive_uniform_error_radius_exists R c eta hc hEta.
exists (Num.min r d);split.
- by rewrite lt_min hr hd.
split.
- by rewrite ge_min lexx.
- change ((Num.min r d)%:E*N<eta%:E)%E.
  rewrite hN -EFinM lte_fin.
  apply:(le_lt_trans _ hCost).
  apply:(ler_wpM2r hc);by rewrite ge_min lexx orbT.
Qed.
