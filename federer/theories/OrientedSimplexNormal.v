(** Earlier source scope: Federer (1969), 4.1.22, p. 379,
    uses the actual simplex currents of 4.1.11, pp. 365–366.
    Their fixed-index normality gives the original inclusion
    diagram in 4.1.24, p. 381. The retained source comments
    also identify their later use in 4.1.32. These prerequisites use the original public simplex operations. *)
(** Federer (1969), 4.1.32, pp. 392–393:
    the original oriented simplex is a normal compact
    current and therefore a flat current. Follow the
    existing Dirac base and original point-join recursion
    of 4.1.11, p. 365. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDirac
  DiracCurrentBounds CurrentDegreeTransportIdentity NormalCurrentsUP FlatCurrentsUP
  CurrentNormalOriginalFlat CurrentJoinSealed CurrentJoinLaws CurrentJoinNormal
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [oriented_simplex_current_normal]: all
    original simplex generators used in 4.1.32,
    pp. 392–393, are normal. Degenerate vertices and
    dimensions above the ambient dimension are retained. *)
Theorem oriented_simplex_current_normal (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  @is_normal_current R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) m
    (@OrientedSimplexCurrent.value R h2 n m v).
Proof.
elim:m v=>[|m ih] v.
- rewrite oriented_simplex_current_point.
  exact:(@dirac_current_normal R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) (v ord0) I).
- pose X:=R_n R n;pose NX:=inner_norm (@euclidean_inner_productP R n).
  pose Full:set X:=fun _=>True.
  pose hFull:=fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x.
  pose P:=@dirac_current R h2 n Full hFull (v ord0).
  pose T:=@OrientedSimplexCurrent.value R h2 n m (current_simplex_tail v).
  have hP:=@dirac_current_normal R h2 n Full hFull (v ord0) I.
  have hT:=ih (current_simplex_tail v).
  have hSimplex:=@oriented_simplex_current_successor R h2 n m v hP.2 hT.2.
  rewrite current_degree_transport_identity in hSimplex.
  rewrite hSimplex.
  exact:(@current_join_normal R h2 n 0%N m P T hP hT).
Qed.

(** Source for [oriented_simplex_current_flat]: the
    actual simplex lies in the original compact flat
    union, as required by the projective-image proof
    of Federer 4.1.32, p. 392. This follows
    from its proved normality and the old inclusion. *)
Theorem oriented_simplex_current_flat (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  @is_flat_current R h2 n m (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x)
    (@OrientedSimplexCurrent.value R h2 n m v).
Proof.
exact:(@current_normal_original_flat R h2 n m (fun _=>True)
  (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) x)
  (@OrientedSimplexCurrent.value R h2 n m v)
  (@oriented_simplex_current_normal R h2 n m v)).
Qed.
