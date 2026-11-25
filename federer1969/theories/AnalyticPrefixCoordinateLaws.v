(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    the original coordinate equations determine the prefix
    maps uniquely. The dual-basis equations prove the
    actual section relation, including empty prefixes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorUP Hom LinearBasis GrassmannAbbreviations FiniteCoordinates AnalyticPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_projection_unique]: the original
    coordinate equation determines p_j, supporting
    3.4.8(1), p. 326. *)
Lemma analytic_prefix_projection_unique (R:realType) (X:lmodType R) n
    (omega:'I_n->Hom X R^o) j (hjn:(j<=n)%N) (P Q:Hom X (R_n R j)):
  is_analytic_prefix_projection omega hjn P ->is_analytic_prefix_projection omega hjn Q ->P=Q.
Proof.
move=>hP hQ;apply:hom_ext=>x;apply/ffunP=>i.
by rewrite hP hQ.
Qed.

(** Source for [analytic_prefix_section_unique]: values on
    the original coordinate basis determine the auxiliary
    inclusion, supporting 3.4.8(1),(5), pp. 326, 328. *)
Lemma analytic_prefix_section_unique (R:realType) (X:lmodType R) n
    (e:'I_n->X) j (hjn:(j<=n)%N) (S T:Hom (R_n R j) X):
  is_analytic_prefix_section e hjn S ->is_analytic_prefix_section e hjn T ->S=T.
Proof.
move=>hS hT;apply:hom_ext.
apply:(@basis_linear_ext R (Choice.clone 'I_j _) (R_n R j) (@coordinate_basis R j)
  (@coordinate_basisP R j) X (hom_as_linear S) (hom_as_linear T))=>i.
by rewrite !hom_as_linearE hS hT.
Qed.

(** Source for [analytic_prefix_projection_section]: the dual
    original bases make the prefix inclusion a section
    of p_j, supporting the coordinate subring and its
    closedness in 3.4.8(1),(5), pp. 326, 328. *)
Theorem analytic_prefix_projection_section (R:realType) (X:lmodType R) n
    (e:'I_n->X) (omega:'I_n->Hom X R^o) j (hjn:(j<=n)%N)
    (P:Hom X (R_n R j)) (S:Hom (R_n R j) X):
  (forall i k,omega i (e k)=if i==k then 1 else 0) ->
  is_analytic_prefix_projection omega hjn P ->is_analytic_prefix_section e hjn S ->
  forall z,P (S z)=z.
Proof.
move=>hDual hP hS.
apply:(@basis_linear_ext R (Choice.clone 'I_j _) (R_n R j) (@coordinate_basis R j)
  (@coordinate_basisP R j) (R_n R j) (hom_as_linear (hom_comp P S)) (linear_id (R_n R j)))=>i.
rewrite hom_as_linearE hom_compE hS.
apply/ffunP=>k.
rewrite hP hDual /coordinate_basis ffunE.
by rewrite -!val_eqE /=.
Qed.
