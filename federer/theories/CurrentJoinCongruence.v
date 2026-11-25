(** Federer (1969), 4.1.11, pp. 364–366: the
    original join depends only on its two currents.
    Equality and compactness-proof independence support
    the simplex and affine-image identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentJoinSealed CurrentJoinLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinCongruence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation C := (fun k=>@current_space R h2 n Full hFull k).
Local Notation Compact := (fun k (T:C k)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull k T)).

(** Source for [current_join_current_congruence]: equal
    original current factors give the same join with every
    compactness witness, supporting Federer 4.1.11,
    pp. 364–366. Only equality elimination and the proved
    independent join law are used. *)
Theorem current_join_current_congruence (S S':C i) (T T':C j)
    (hS:Compact i S) (hS':Compact i S') (hT:Compact j T) (hT':Compact j T'):
  S=S'->T=T'->@CurrentJoin.value R h2 n i j S T hS hT=
    @CurrentJoin.value R h2 n i j S' T' hS' hT'.
Proof.
move=>hFirst hSecond;subst S';subst T'.
exact:(@current_join_proof_independent R h2 n i j S T hS hT hS' hT').
Qed.
End CurrentJoinCongruence.
