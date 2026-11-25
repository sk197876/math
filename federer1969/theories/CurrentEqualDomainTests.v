(** Federer (1969), 4.1.18, p. 374: genuine
    compact tests and their actions are unchanged
    by equal presentations of the same open domain.
    This internal equality adapter keeps homotopy
    geometry proofs out of caller hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDomainTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
(** Source for [current_test_equal_domain]: equality alone
    identifies the original test spaces, supporting
    the smoothing homotopies of 4.1.18, p. 374. *)
Definition current_test_equal_domain (R:realType) (h2:(1+1:R)!=0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U=V):
    Hom (@current_test_space R h2 n U hU m)
      (@current_test_space R h2 n V hV m).
Proof.
destruct e.
exact:(eq_rect_r
  (fun hV=>Hom (@current_test_space R h2 n U hU m)
    (@current_test_space R h2 n U hV m))
  (hom_of_linear (@linear_id R (@current_test_space R h2 n U hU m)))
  (Prop_irrelevance hV hU)).
Defined.

(** Source for [current_test_equal_domain_values]: the
    actual compact test coefficients stay identical,
    supporting 4.1.18, p. 374, including empty U. *)
Theorem current_test_equal_domain_values
    (R:realType) (h2:(1+1:R)!=0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U=V)
    (omega:@current_test_space R h2 n U hU m) x:
  @current_test_value R h2 n V hV m (@current_test_equal_domain R h2 n m U V hU hV e omega) x=
  @current_test_value R h2 n U hU m omega x.
Proof.
subst V;have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
rewrite /current_test_equal_domain.
try rewrite (Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU)).
reflexivity.
Qed.

(** Source for [current_equal_domain_test_action]: the
    transported current and transported compact test
    have their original pairing, supporting
    4.1.18, p. 374. *)
Theorem current_equal_domain_test_action
    (R:realType) (h2:(1+1:R)!=0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U=V)
    (T:@current_space R h2 n U hU m)
    (omega:@current_test_space R h2 n U hU m):
  @current_value R h2 n V hV m
    (@current_domain_transport R h2 n U hU V e hV m T)
    (@current_test_equal_domain R h2 n m U V hU hV e omega)=
  @current_value R h2 n U hU m T omega.
Proof.
subst V;have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
rewrite current_domain_transport_refl /current_test_equal_domain.
try rewrite (Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU)).
reflexivity.
Qed.


(** Source for [current_equal_domain_test_action_reverse]:
    the same original pairing law with a test
    initially presented on the target domain,
    supporting the literal integrals of 4.1.18,
    p. 374. No action on noncompact forms occurs. *)
Theorem current_equal_domain_test_action_reverse
    (R:realType) (h2:(1+1:R)!=0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U=V)
    (T:@current_space R h2 n U hU m)
    (omega:@current_test_space R h2 n V hV m):
  @current_value R h2 n V hV m
    (@current_domain_transport R h2 n U hU V e hV m T) omega=
  @current_value R h2 n U hU m T
    (@current_test_equal_domain R h2 n m V U hV hU (esym e) omega).
Proof.
destruct e;have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
rewrite (Prop_irrelevance (esym (erefl U)) (erefl U)).
rewrite current_domain_transport_refl /current_test_equal_domain.
try rewrite (Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU)).
reflexivity.
Qed.
