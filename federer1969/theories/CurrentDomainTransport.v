(** Federer (1969), 4.1.11, p. 366: identify
    equal presentations of the original containing domain.
    In particular the full Cartesian domain is the full
    Euclidean space. This is equality transport only;
    no new current space or mathematical choice is made. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentDirac CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDomainTransport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation Open := (fun U:set X=>forall x,U x->norm_domain_interior NX U x).
Variable U:set X.
Hypothesis hU:Open U.

(** Source for [current_domain_transport]: equality
    identifies two presentations of the same original
    domain in Federer 4.1.11, p. 366. The map is
    the identity linear map after equality elimination. *)
Definition current_domain_transport (V:set X) (e:U=V) (hV:Open V) k:
    Hom (@current_space R h2 n U hU k) (@current_space R h2 n V hV k).
Proof.
destruct e.
exact:(eq_rect_r
  (fun hV=>Hom (@current_space R h2 n U hU k) (@current_space R h2 n U hV k))
  (hom_of_linear (@linear_id R (@current_space R h2 n U hU k)))
  (Prop_irrelevance hV hU)).
Defined.
Arguments current_domain_transport {V} e hV {k}.

(** Source for [current_domain_transport_refl]: transporting
    through the identical original domain fixes every
    current, supporting Federer 4.1.11, p. 366. *)
Lemma current_domain_transport_refl k (T:@current_space R h2 n U hU k):
  current_domain_transport (erefl U) hU T=T.
Proof.
rewrite /current_domain_transport /=.
rewrite (Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU)).
reflexivity.
Qed.

(** Source for [current_domain_transport_support]: the
    actual ambient support is unchanged by an equal
    domain presentation, supporting Federer 4.1.11, p. 366. *)
Theorem current_domain_transport_support (V:set X) (e:U=V) (hV:Open V) k
    (T:@current_space R h2 n U hU k):
  @current_support R h2 n V hV k (current_domain_transport e hV T)=
    @current_support R h2 n U hU k T.
Proof.
subst V.
have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
by rewrite current_domain_transport_refl.
Qed.

(** Source for [current_domain_transport_boundary]:
    equality of the containing domain preserves the
    original boundary, supporting the top-degree prism
    argument in Federer 4.1.11, p. 366. *)
Theorem current_domain_transport_boundary (V:set X) (e:U=V) (hV:Open V) k
    (T:@current_space R h2 n U hU k.+1):
  current_domain_transport e hV (@current_boundary R h2 n k U hU T)=
    @current_boundary R h2 n k V hV (current_domain_transport e hV T).
Proof.
subst V.
have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
by rewrite !current_domain_transport_refl.
Qed.

(** Source for [current_domain_transport_dirac]: the
    same original point current is retained by an equal
    domain presentation, supporting Federer 4.1.11, p. 366. *)
Theorem current_domain_transport_dirac (V:set X) (e:U=V) (hV:Open V) u:
  current_domain_transport e hV (@dirac_current R h2 n U hU u)=
    @dirac_current R h2 n V hV u.
Proof.
subst V.
have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
by rewrite current_domain_transport_refl.
Qed.
End CurrentDomainTransport.
