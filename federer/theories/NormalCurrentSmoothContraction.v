(** Federer (1969), 4.1.17, p. 374: the smooth-form
    approximations act on flat chains through normal-current
    approximations. Smooth contraction preserves normality by
    the original boundary identity of 4.1.7, p. 356, and the
    original local normality and support definitions on p. 358. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentContraction CurrentContractionSupport
  CurrentBoundaryContraction SmoothCurrentExteriorDerivative CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentIntegrationCriterion
  CurrentRepresentableLinear CurrentRepresentableDegreeTransport
  CurrentRepresentableSmoothProducts NormalCurrentsUP CurrentSupportGeometry
  SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NormalCurrentSmoothContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C d := (@current_space R h2 n U hU d).
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation represented d := (@is_integration_representable_current
  R h2 n d U hU).
Local Notation localnormal d := (@is_locally_normal_current R h2 n U hU d).
Local Notation normal d := (@is_normal_current R h2 n U hU d).
Local Notation P a b := (@current_contraction R h2 n a b U hU).
Local Notation bd d := (@current_boundary R h2 n d U hU).
Local Notation d a := (@smooth_current_exterior_derivative R h2 n a U hU).
Local Notation Tr a b e := (@current_degree_transport R h2 n U hU a b e).

(** Source for [locally_normal_current_degree_transport]: equal
    original degrees preserve local normality, supporting the
    boundary-contraction identity of 4.1.7, p. 356, in Federer
    4.1.17, p. 374. Only equality of natural degrees is used. *)
Lemma locally_normal_current_degree_transport a b (e:a=b) (T:C a):
  localnormal a T->localnormal b (Tr a b e T).
Proof. by case:b /e in T *. Qed.

(** Source for [locally_normal_smooth_contraction_positive]: the
    boundary of an original smooth contraction is representable
    by the signed difference of the two original contractions
    in 4.1.7, p. 356. This supports the smooth coefficient step
    in Federer 4.1.17, p. 374. The output has positive degree. *)
Lemma locally_normal_smooth_contraction_positive k p
    (gamma:E k) (T:C (k+p).+1):
  localnormal (k+p).+1 T->
  localnormal p.+1 (P k p.+1 gamma (Tr _ _ (esym (addnS k p)) T)).
Proof.
move=>[hT hBT];split.
- apply:(@current_contraction_represented R h2 n k p.+1 U hU gamma).
  exact:(@represented_current_degree_transport R h2 n U hU
    (k+p).+1 (k+p.+1) (esym (addnS k p)) T hT).
- pose A:=P k p gamma (bd (k+p) T).
  pose B:=P k.+1 p (d k gamma) (Tr _ _ (esym (addSn k p)) T).
  pose Q:=bd p (P k p.+1 gamma (Tr _ _ (esym (addnS k p)) T)).
  have hA:represented p A.
    exact:(@current_contraction_represented R h2 n k p U hU gamma
      (bd (k+p) T) hBT).
  have hB:represented p B.
    apply:(@current_contraction_represented R h2 n k.+1 p U hU (d k gamma)).
    exact:(@represented_current_degree_transport R h2 n U hU
      (k+p).+1 (k.+1+p) (esym (addSn k p)) T hT).
  have hFormula:A=B+(-1:R)^+k*:Q:=
    @current_boundary_contraction R h2 n k p U hU T gamma.
  have hSigned:(-1:R)^+k*:Q=A-B.
    by rewrite hFormula addrAC subrr add0r.
  have hDifference:=@represented_current_difference R h2 n p U hU
    A B hA hB.
  rewrite -hSigned in hDifference.
  have h:=@represented_current_linear R h2 n p U hU ((-1:R)^+k)
    ((-1:R)^+k*:Q) (0:C p) hDifference
    (@represented_current_zero R h2 n p U hU).
  by rewrite scalerA -expr2 sqrr_sign scale1r addr0 in h.
Qed.

(** Source for [locally_normal_smooth_contraction]: every original
    smooth k-form contraction of a locally normal (k+p)-current
    is locally normal, by the original identities of 4.1.7,
    pp. 356–358; supporting Federer 4.1.17, p. 374. The separate
    output-degree-zero case has no negative-degree boundary. *)
Theorem locally_normal_smooth_contraction k p (gamma:E k) (T:C (k+p)):
  localnormal (k+p) T->localnormal p (P k p gamma T).
Proof.
case:p T=>[|q] T hT.
- split;last by [].
  exact:(@current_contraction_represented R h2 n k 0%N U hU gamma T hT.1).
- pose T0:=Tr _ _ (addnS k q) T.
  have hT0:localnormal (k+q).+1 T0.
    exact:(@locally_normal_current_degree_transport (k+q.+1) (k+q).+1
      (addnS k q) T hT).
  have h:=locally_normal_smooth_contraction_positive gamma hT0.
  by rewrite /T0 current_degree_transport_roundtrip in h.
Qed.

(** Source for [normal_current_smooth_contraction]: smooth
    contraction preserves the original normal-current class,
    by its local normality and unchanged compact support bound,
    supporting Federer 4.1.17, p. 374. The coefficient need not
    itself have compact support. All admissible degrees remain. *)
Theorem normal_current_smooth_contraction k p (gamma:E k) (T:C (k+p)):
  normal (k+p) T->normal p (P k p gamma T).
Proof.
move=>hNormal;split.
- exact:(@locally_normal_smooth_contraction k p gamma T hNormal.1).
- pose K:=@Build_smooth_compact_set R X NX hNX U
    (@current_support R h2 n U hU (k+p) T) (fun x hx=>hx.1) hNormal.2.
  apply:(@current_support_compact_bound R h2 n p U hU K (P k p gamma T)).
  exact:(@current_contraction_support_subset R h2 n k p U hU gamma T).
Qed.
End NormalCurrentSmoothContraction.
