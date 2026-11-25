(** Federer (1969), 4.1.23, pp. 379–380:
    the coordinate product presentation and its
    equal full Euclidean domain give exactly
    the same original compact flat norm.
    Only domain equality and equality of
    the actual compact carrier are transported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDomainTransport CurrentDegreeTransport CurrentDegreeTransportIdentity
  CurrentFlatNorm SmoothCompactSet
  SmoothCompactSetExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_equal_domain_flat_norm]:
    the original F_A used in Federer
    4.1.23, p. 380, is
    unchanged by equal Cartesian/full-domain
    presentations with the same compact A.
    No new flat topology or carrier
    equality premise is introduced. *)
Theorem current_equal_domain_flat_norm (R : realType)
    (h2 : (1+1:R)!=0) n m (U V : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV : forall x, V x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e : U=V)
    (K : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (L : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) V)
    (hKL : smooth_compact_carrier K=smooth_compact_carrier L)
    (T : @current_space R h2 n U hU m) :
  @current_flat_norm R h2 n m V hV L
    (@current_domain_transport R h2 n U hU V e hV m T)=
      @current_flat_norm R h2 n m U hU K T.
Proof.
subst V; have hProof : hV=hU := Prop_irrelevance _ _; subst hV.
have hIndex : K=L := smooth_compact_set_extensionality hKL.
by rewrite current_domain_transport_refl hIndex.
Qed.

(** Source for [current_equal_degree_flat_norm]:
    the harmless identification m+0=m in
    Federer 4.1.23, p. 380,
    leaves the original compact flat
    norm unchanged. All natural degrees
    and all actual currents are retained. *)
Theorem current_equal_degree_flat_norm (R : realType)
    (h2 : (1+1:R)!=0) n (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    m j (e : m=j) (T : @current_space R h2 n U hU m) :
  @current_flat_norm R h2 n j U hU K
    (@current_degree_transport R h2 n U hU m j e T)=
      @current_flat_norm R h2 n m U hU K T.
Proof. by case: j/e; rewrite current_degree_transport_identity. Qed.
