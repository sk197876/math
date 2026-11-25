(** Federer (1969), 4.1.8, p. 361: use the
    original mass and comass laws at arbitrary positive
    total degrees. These adapters expose the already proved
    4.1.7 coefficient norms without a new norm definition. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  CurrentCoefficientNorms ComassUP Comass MassUP Mass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_positive_comass_laws]: in every
    positive degree the actual covector norm satisfies the
    original comass specification, supporting Federer 4.1.8,
    p. 361, by 1.8.1, p. 38. *)
Lemma current_positive_comass_laws (R:realType) (h2:(1+1:R)!=0) n d
    (hd:(0<d)%N) (phi:A_m (R_n R n) R^o d):
  is_comass h2 (@euclidean_inner_productP R n) phi (@current_form_comass R h2 n d phi).
Proof. case:d phi hd=>[|k] phi hd;first by []. exact:comassP. Qed.

(** Source for [current_positive_mass_laws]: in every
    positive degree the actual vector norm satisfies the
    original mass specification, supporting Federer 4.1.8,
    p. 361, by 1.8.1, p. 38. *)
Lemma current_positive_mass_laws (R:realType) (h2:(1+1:R)!=0) n d
    (hd:(0<d)%N) (x:exterior_power (R_n R n) d):
  is_mass (@current_form_comass R h2 n d) x (@current_vector_mass R h2 n d x).
Proof. case:d x hd=>[|k] x hd;first by []. exact:massP. Qed.
