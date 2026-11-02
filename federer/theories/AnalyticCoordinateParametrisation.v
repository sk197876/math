(** Federer (1969), 3.1.24, p. 240, referring to 3.1.19, p. 231: condition (4) implies (3).
    Differentiate phi psi=id to get full source rank; images of open
    parameter subsets are B intersect an ambient open inverse image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom TensorUP FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness LinearRankUP LinearInjectiveRank
  NormDifferentialUP NormDifferentialInverseIdentities NormClassOneUP NormRegularity
  NormOpenPreimage EuclideanSubmanifoldUP SubmanifoldChartsUP NormAnalyticUP NormAnalyticLocal AnalyticSubmanifoldChartsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_convex_coordinates_open_parametrisations]: 3.1.24, p. 240: the
    implication (4) to (3) in Federer 3.1.19, p. 231. The parameter
    dimension is mu. The rank identity is proved by the chain rule,
    and the relative openness uses the printed inverse-image identity. *)
Theorem analytic_convex_coordinates_open_parametrisations (R:realType) n mu (B:set (R_n R n)) :
  @has_analytic_convex_coordinates R n mu B ->
  @has_analytic_open_parametrisations R n mu B.
Proof.
move=>hB b hb.
have [T [V [phi [psi [hTb [hV [hphi [hpsi [hphiV [hpsiT [him hcan]]]]]]]]]]]:=hB b hb.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hphi1:=norm_analytic_class_all_orders hphi 1%N.
have hpsi1:=norm_analytic_class_all_orders hpsi 1%N.
have [D hD]:=(norm_class_firstP hNY hNX V psi).1 hpsi1.
have [E hE]:=(norm_class_firstP hNX hNY T phi).1 hphi1.
have hpsiB u (hu:V u):B (psi u).
  have hi:(psi @` V) (psi u) by exists u.
  rewrite him in hi; exact hi.1.
have hr u (hu:V u):has_linear_rank (D u) mu.
  have hleft:=@norm_differentials_left_inverse R (R_n R mu) (R_n R n) NY NX hNY hNX
    V T psi phi u (D u) (E (psi u)) hpsiT hcan
    (@norm_class_one_differential R (R_n R mu) (R_n R n) NY NX V psi D hD u hu)
    (@norm_class_one_differential R (R_n R n) (R_n R mu) NX NY T phi E hE (psi u) (hpsiT u hu)).
  refine (@linear_injective_rank R (R_n R mu) (R_n R n) mu
    (@coordinate_basis R mu) (@coordinate_basisP R mu) n
    (@coordinate_basis R n) (@coordinate_basisP R n) (D u) _).
  move=>x y hxy.
  have hx:=congr1 (fun L:Hom (R_n R mu) (R_n R mu)=>L x) hleft.
  have hy:=congr1 (fun L:Hom (R_n R mu) (R_n R mu)=>L y) hleft.
  rewrite hom_compE hxy hom_of_linearE /= in hx.
  rewrite hom_compE hom_of_linearE /= in hy.
  exact (eq_trans (esym hx) hy).
exists mu,V,psi,D; split; first exact: leqnn.
split=>//; split=>//; split; first exact hpsiB.
split.
- have hbT:T b:=norm_domain_interior_member hNX hTb.
  rewrite him; exact: conj hb hbT.
split; first exact hr.
move=>W hWV hW.
exists [set x|T x /\ W (phi x)]; split.
- exact (@norm_class_zero_open_preimage R (R_n R n) (R_n R mu) NX NY hNX hNY
    T W phi (norm_class_continuous hphi1) hW).
- apply/seteqP; split=>x.
  + move=>[u hu <-]; split; first exact: hpsiB (hWV u hu).
    split; first exact: hpsiT (hWV u hu).
    by rewrite hcan //; exact: hWV.
  + move=>[hBx [hTx hWx]].
    have hi:(psi @` V) x by rewrite him; split.
    have [u hu hux]:=hi.
    exists u=>//.
    by rewrite -hux hcan in hWx.
Qed.
