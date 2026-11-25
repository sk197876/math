(** Federer (1969), 4.1.7, p. 356: equal-degree
    bookkeeping for the original current identities.
    These transports identify equal natural degrees;
    they introduce no negative-degree currents. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms ExteriorHomogeneousProducts CurrentSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation DT := (fun m=>@current_test_space R h2 n U hU m).
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).

(** Source for [current_degree_transport]: identify
    exactly equal original current dimensions,
    supporting Federer 4.1.7, p. 356. *)
Definition current_degree_transport m q (h:m=q):Hom (C m) (C q).
Proof.
case:q /h; exact:(@HomMap R (C m) (C m) (fun T=>T) (introT (asboolP _) (fun c T S=>erefl))).
Defined.

(** Source for [current_test_degree_transport]: identify
    exactly equal original test degrees, supporting
    Federer 4.1.7, p. 356. *)
Definition current_test_degree_transport m q (h:m=q):Hom (DT m) (DT q).
Proof.
case:q /h; exact:(@HomMap R (DT m) (DT m) (fun f=>f) (introT (asboolP _) (fun c f g=>erefl))).
Defined.

(** Source for [current_smooth_degree_transport]: identify
    equal original smooth-form degrees, supporting
    Federer 4.1.7, p. 356. *)
Definition current_smooth_degree_transport m q (h:m=q):Hom (E m) (E q).
Proof.
case:q /h; exact:(@HomMap R (E m) (E m) (fun f=>f) (introT (asboolP _) (fun c f g=>erefl))).
Defined.

(** Source for [current_degree_transport_evaluation]:
    equal-degree identification preserves actual test
    action, supporting Federer 4.1.7, p. 356. *)
Lemma current_degree_transport_evaluation m q (h:m=q) T phi:
  @current_value R h2 n U hU q (current_degree_transport h T) phi=
    @current_value R h2 n U hU m T (current_test_degree_transport (esym h) phi).
Proof. by case:q /h in T phi *. Qed.

(** Source for [current_degree_reverse_evaluation]:
    the reverse current identification is the
    transpose of the forward test identification,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_degree_reverse_evaluation m q (h:m=q) T phi:
  @current_value R h2 n U hU m (current_degree_transport (esym h) T) phi=
    @current_value R h2 n U hU q T (current_test_degree_transport h phi).
Proof. by case:q /h in T *. Qed.

(** Source for [current_test_degree_transport_values]:
    equal-degree identification preserves the original
    form values, supporting Federer 4.1.7, p. 356. *)
Lemma current_test_degree_transport_values m q (h:m=q) phi x:
  @current_test_value R h2 n U hU q (current_test_degree_transport h phi) x=
    form_reindex h (@current_test_value R h2 n U hU m phi x).
Proof. by case:q /h. Qed.

(** Source for [current_smooth_degree_transport_values]:
    equal-degree identification preserves original
    smooth values, supporting Federer 4.1.7, p. 356. *)
Lemma current_smooth_degree_transport_values m q (h:m=q) phi x:
  @current_smooth_value R h2 n U hU q (current_smooth_degree_transport h phi) x=
    form_reindex h (@current_smooth_value R h2 n U hU m phi x).
Proof. by case:q /h. Qed.
End CurrentDegreeTransport.
