(** Federer (1969), 4.1.18, p. 375: independent
    specification of q(xi,eta)=Lebesgue^n wedge xi+
    boundary(Lebesgue^n wedge eta). The source uses the
    actual compactly supported L1 fields, and the two
    density currents are already specified opaque objects. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CompactSummableMultivectors
  CompactSummableMultivectorDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PairImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation A:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation B:=(@compact_summable_multivector_space R h2 n m.+1 U hU).

(** Source for [current_lone_pair_space]: the source
    Omega_m(U) times Omega_(m+1)(U) of q, Federer
    4.1.18, p. 375. Its integral cost J is
    specified separately on these same original factors. *)
Definition current_lone_pair_space:lmodType R:=
  [the lmodType R of (A*B)%type].

(** Source for [is_current_lone_pair_map]: the exact
    defining equation for the original linear q,
    Federer 4.1.18, p. 375. Existence, range and
    kernel conclusions are separate theorems. *)
Definition is_current_lone_pair_map
    (Q:Hom current_lone_pair_space (@current_space R h2 n U hU m)):Prop:=
  forall v:current_lone_pair_space,
    Q v=@compact_summable_multivector_current R h2 n m U hU v.1+
      @current_boundary R h2 n m U hU
        (@compact_summable_multivector_current R h2 n m.+1 U hU v.2).

(** Source for [current_lone_pair_map_unique]: q is
    determined by its original density and boundary
    equation, Federer 4.1.18, p. 375. *)
Theorem current_lone_pair_map_unique
    (Q P:Hom current_lone_pair_space (@current_space R h2 n U hU m)):
  is_current_lone_pair_map Q->is_current_lone_pair_map P->Q = P.
Proof. move=>hQ hP;apply:hom_ext=>v;exact:(eq_trans (hQ v) (esym (hP v))). Qed.
End PairImage.
