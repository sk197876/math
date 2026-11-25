(** Federer (1969), 4.1.7, p. 358: finite
    normal mass implies local normality. Both
    positive-degree masses are nonnegative, so
    finiteness of their sum gives the two
    finite-mass representation hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentIntegrationCriterion
  CurrentMassSealed CurrentMassBasic CurrentFiniteMassRepresentation NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentNormalMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation M := (fun m=>@CurrentMass.value R h2 n m U hU).
Local Notation N := (@current_normal_mass R h2 n U hU).
Local Notation bd := (fun m=>@current_boundary R h2 n m U hU).

(** Source for [current_normal_mass_zero_degree]:
    the exact original N(T)=M(T) convention
    in degree zero, Federer 4.1.7, p. 358. *)
Lemma current_normal_mass_zero_degree (T:C 0):N T=M 0 T.
Proof. by []. Qed.

(** Source for [current_normal_mass_positive_degree]:
    N(T)=M(T)+M(boundary T) in every
    positive degree, Federer 4.1.7, p. 358. *)
Lemma current_normal_mass_positive_degree m (T:C m.+1):
  N T=(M m.+1 T+M m (bd m T))%E.
Proof. by []. Qed.

(** Source for [current_normal_mass_nonnegative]:
    the original normal mass is nonnegative,
    supporting Federer 4.1.7, p. 358. *)
Theorem current_normal_mass_nonnegative m (T:C m):(0<=N T)%E.
Proof.
case:m T=>[|d] T.
- exact:current_mass_nonnegative.
- exact:adde_ge0 (@current_mass_nonnegative R h2 n d.+1 U hU T)
    (@current_mass_nonnegative R h2 n d U hU (bd d T)).
Qed.

(** Source for [finite_normal_mass_locally_normal]:
    if N(T)<infinity then T is locally
    normal, Federer 4.1.7, p. 358,
    paragraph following the definition of N.
    The zero-degree case uses only M(T). *)
Theorem finite_normal_mass_locally_normal m (T:C m):
  (N T < +oo)%E->@is_locally_normal_current R h2 n U hU m T.
Proof.
case:m T=>[|d] T hFinite.
- split;last by [].
  exact:(@current_finite_mass_representation R h2 n 0 U hU T hFinite).
- have hA:=@current_mass_nonnegative R h2 n d.+1 U hU T.
  have hB:=@current_mass_nonnegative R h2 n d U hU (bd d T).
  have hLeft:(M d.+1 T<=M d.+1 T+M d (bd d T))%E.
    rewrite -[leLHS](adde0 (M d.+1 T));exact:leeD2l hB.
  have hRight:(M d (bd d T)<=M d.+1 T+M d (bd d T))%E.
    rewrite addeC -[leLHS](adde0 (M d (bd d T)));exact:leeD2l hA.
  split.
  + exact:(@current_finite_mass_representation R h2 n d.+1 U hU T
      (le_lt_trans hLeft hFinite)).
  + exact:(@current_finite_mass_representation R h2 n d U hU (bd d T)
      (le_lt_trans hRight hFinite)).
Qed.
End CurrentNormalMass.
